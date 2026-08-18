#!/usr/bin/env python3
"""Run the staged Lean implementation loop for Allender OQ3.

The conveyor is exactly:

    Gemini 3.1 Pro High -> Claude Opus 4.8 -> Aristotle

Every Nth iteration starting at ``--strategy-first`` is strategic and plans
the next N-1 proof iterations. Aristotle receives a strategic packet on those
iterations too.

The exact model, incidence certificate, principle signatures, and final
statement are checksum-frozen.  The agents close the two remaining proof bodies.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import datetime as dt
import filecmp
try:
    import fcntl
except ImportError:  # pragma: no cover - production is pinned to the Linux VM
    fcntl = None
import hashlib
import json
import os
import re
import signal
import stat
from pathlib import Path
from pathlib import PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import time
import traceback
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOF_LOOP_DIR = ROOT / "proof_loop"
SECTIONS_PATH = PROOF_LOOP_DIR / "sections.json"
DEFAULT_RUNS_DIR = ROOT / "proof_loop_runs"
DEFAULT_STOP_FILE = PROOF_LOOP_DIR / "PAUSE"
GEMINI_MODEL = "gemini-3.1-pro-high"
GEMINI_EFFORT = "high"
CLAUDE_MODEL = "claude-opus-4-6-thinking"
CLAUDE_EFFORT = "none"
EXPECTED_AGY_BIN = Path("/home/lesha/.local/bin/agy")
EXPECTED_CLAUDE_BIN = Path("/home/lesha/.npm-global/bin/claude")
ARISTOTLE_BIN = Path("/home/lesha/.local/bin/aristotle")
PROTECTED_PATHS = (
    "AllenderOQ3/Model.lean",
    "AllenderOQ3/Incidence.lean",
    "AllenderOQ3/Principles.lean",
    "AllenderOQ3/Statement.lean",
    "Main.lean",
    "README.md",
    "FORMALIZATION_PLAN.md",
    "docs/MATHEMATICAL_PROOF.md",
    "docs/EXTERNAL_FACTS.md",
    "docs/INCIDENCE_REFINEMENT.md",
    "docs/EXTERNAL_FACTS_FORMALIZATION_PLAN.md",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "proof_loop/frozen_api.sha256",
    "proof_loop/dependency_tree.sha256",
    "proof_loop/sections.json",
    "scripts/check_trust.py",
    "scripts/check_dependencies.py",
    "scripts/audit.sh",
    "scripts/audit_release.sh",
    "scripts/run_proof_pipeline.py",
    "scripts/launch_pipeline.sh",
    "scripts/resume_pipeline.sh",
    "scripts/dry_run_pipeline.sh",
    "scripts/test_pipeline_safety.py",
)
PROTECTED_SNAPSHOT: dict[str, bytes] = {}
CANONICAL_TREE_SNAPSHOT: dict[str, bytes] = {}
CANONICAL_RUNTIME_FILES = {
    "proof_loop/RUNNER_PID",
    "proof_loop/ACTIVE_RUN",
    "proof_loop/MERGE_GATE.lock",
    "proof_loop/MERGE_JOURNAL.json",
    "proof_loop/RUNNER.lock",
    "proof_loop/axiom_report.txt",
}
ARISTOTLE_CONTROL_NAMES = (
    "aristotle_state.json",
    "aristotle_result.tar.gz",
    "aristotle_result.download.tmp",
    "aristotle_prompt.md",
    "submit_aristotle.py",
    "aristotle_submit.log",
    "aristotle_followup.log",
)
BLOCKING_STATUSES = {
    "blocked_protected_file_change",
    "blocked_canonical_protected_file_change",
    "blocked_direct_canonical_change",
    "blocked_canonical_dependency_change",
    "blocked_agent_control_file_change",
}
RUNNER_LOCK_HANDLE: Any | None = None
DEFAULT_STABILITY_LAB_ROOT = Path("/home/lesha/harper-stability-lab")


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def read_text(path: Path, max_chars: int | None = None) -> str:
    if not path.exists():
        return f"[missing: {path}]\n"
    text = path.read_text(encoding="utf-8", errors="replace")
    if max_chars is not None and len(text) > max_chars:
        return text[:max_chars] + f"\n\n[TRUNCATED at {max_chars} chars from {path}]\n"
    return text


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def fsync_directory(path: Path) -> None:
    """Persist a completed rename in its parent directory on POSIX."""
    if os.name != "posix":
        return
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    fd = os.open(path, flags)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def acquire_runner_lock() -> None:
    """Hold one process-wide lock before any resumable remote state is read."""
    global RUNNER_LOCK_HANDLE
    if fcntl is None:
        raise RuntimeError("the proof conveyor requires POSIX fcntl locking")
    PROOF_LOOP_DIR.mkdir(parents=True, exist_ok=True)
    handle = open_nofollow_lock(PROOF_LOOP_DIR / "RUNNER.lock")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        handle.close()
        raise RuntimeError("another OQ3 proof conveyor already holds RUNNER.lock") from exc
    handle.seek(0)
    handle.truncate()
    handle.write(f"pid={os.getpid()} started={utc_now()}\n")
    handle.flush()
    os.fsync(handle.fileno())
    fsync_directory(PROOF_LOOP_DIR)
    RUNNER_LOCK_HANDLE = handle


def open_nofollow_lock(path: Path):
    """Open a regular lock file without ever following a stale symlink."""
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(path, flags, 0o600)
    if not stat.S_ISREG(os.fstat(fd).st_mode):
        os.close(fd)
        raise RuntimeError(f"lock path is not a regular file: {path}")
    os.fchmod(fd, 0o600)
    return os.fdopen(fd, "r+", encoding="utf-8")


def write_json(path: Path, data: Any) -> None:
    """Atomically replace a JSON state file, including after power loss."""
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(data, indent=2, ensure_ascii=False) + "\n"
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def atomic_copy(source: Path, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{target.name}.", suffix=".tmp", dir=target.parent)
    os.close(fd)
    try:
        shutil.copy2(source, temporary)
        with open(temporary, "rb") as handle:
            os.fsync(handle.fileno())
        os.replace(temporary, target)
        fsync_directory(target.parent)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def recover_incomplete_merge() -> dict[str, Any] | None:
    journal = ROOT / "proof_loop/MERGE_JOURNAL.json"
    if not os.path.lexists(journal):
        return None
    if journal.is_symlink() or not journal.is_file():
        raise RuntimeError(f"unsafe merge recovery journal: {journal}")
    try:
        data = json.loads(journal.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"invalid merge recovery journal JSON: {journal}") from exc
    if not isinstance(data, dict) or "entries" not in data:
        raise RuntimeError("merge recovery journal must be an object with entries")
    entries = data["entries"]
    if not isinstance(entries, list) or not entries:
        raise RuntimeError("invalid merge recovery journal")
    restored: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise RuntimeError("invalid merge recovery entry")
        if "rel" not in entry or "existed" not in entry or type(entry["existed"]) is not bool:
            raise RuntimeError("merge recovery entry requires rel and Boolean existed")
        rel = str(entry.get("rel", ""))
        if "\\" in rel:
            raise RuntimeError(f"invalid merge recovery path: {rel}")
        pure = PurePosixPath(rel)
        if pure.is_absolute() or not pure.parts or ".." in pure.parts or "." in pure.parts:
            raise RuntimeError(f"invalid merge recovery path: {rel}")
        rel = pure.as_posix()
        if rel in seen:
            raise RuntimeError(f"duplicate merge recovery path: {rel}")
        seen.add(rel)
        recovery_allowed = (
            rel.startswith("AllenderOQ3/Internal/")
            or rel in {
                "AllenderOQ3/Target.lean",
                "AllenderOQ3.lean",
                "COVERAGE.md",
                "proof_loop/COMPLETE.oq3",
            }
        )
        if not recovery_allowed:
            raise RuntimeError(f"merge recovery path is not allowlisted: {rel}")
        target = safe_project_target(ROOT, rel)
        backup = Path(str(entry.get("backup", ""))) if entry.get("backup") else None
        if entry["existed"]:
            if backup is None or backup.is_symlink() or not backup.is_file():
                raise RuntimeError(f"missing merge backup for {rel}")
            expected_suffix = ("merge_gate", "backup", *pure.parts)
            if tuple(backup.parts[-len(expected_suffix):]) != expected_suffix:
                raise RuntimeError(f"invalid merge backup location for {rel}: {backup}")
            expected_hash = entry.get("backup_sha256")
            actual_hash = hashlib.sha256(backup.read_bytes()).hexdigest()
            if not expected_hash or actual_hash != expected_hash:
                raise RuntimeError(f"merge backup checksum mismatch for {rel}")
            atomic_copy(backup, target)
        else:
            if entry.get("backup") is not None or entry.get("backup_sha256") is not None:
                raise RuntimeError(f"unexpected backup for non-existing merge target: {rel}")
        if not entry["existed"] and os.path.lexists(target):
            if target.is_symlink():
                raise RuntimeError(f"refusing symlink during merge recovery: {target}")
            if target.is_dir():
                raise RuntimeError(f"refusing to remove directory during merge recovery: {target}")
            target.unlink()
        restored.append(rel)
    journal.unlink()
    return {"restored": restored, "journal": str(journal)}


def protected_mismatches(candidate_root: Path) -> list[str]:
    """Compare trust-critical files against the canonical live root.

    The checker and its manifest inside an agent worktree are untrusted input;
    this comparison is performed by the already-running canonical runner.
    """
    mismatches: list[str] = []
    for rel in PROTECTED_PATHS:
        try:
            candidate = safe_project_target(candidate_root, rel)
        except RuntimeError:
            mismatches.append(rel)
            continue
        expected = PROTECTED_SNAPSHOT.get(rel)
        if expected is None or not candidate.is_file():
            mismatches.append(rel)
        elif candidate.read_bytes() != expected:
            mismatches.append(rel)
    return mismatches


def restore_protected(candidate_root: Path, paths: list[str]) -> None:
    for rel in paths:
        target = safe_project_target(candidate_root, rel)
        target.parent.mkdir(parents=True, exist_ok=True)
        expected = PROTECTED_SNAPSHOT.get(rel)
        if expected is None:
            raise RuntimeError(f"missing in-memory protected snapshot for {rel}")
        fd, temporary = tempfile.mkstemp(prefix=f".{target.name}.", suffix=".tmp", dir=target.parent)
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(expected)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, target)
            fsync_directory(target.parent)
        finally:
            try:
                os.unlink(temporary)
            except FileNotFoundError:
                pass


def safe_project_target(root: Path, rel: str) -> Path:
    """Return a lexical in-project target and reject symlinked path components."""
    if "\\" in rel:
        raise RuntimeError(f"unsafe project path: {rel}")
    pure = PurePosixPath(rel)
    if pure.is_absolute() or not pure.parts or ".." in pure.parts or "." in pure.parts:
        raise RuntimeError(f"unsafe project path: {rel}")
    root_resolved = root.resolve()
    cursor = root
    for part in pure.parts[:-1]:
        cursor = cursor / part
        if cursor.is_symlink():
            raise RuntimeError(f"symlinked project parent: {cursor}")
    target = root / Path(*pure.parts)
    if target.is_symlink():
        raise RuntimeError(f"symlinked project target: {target}")
    parent = target.parent
    parent.mkdir(parents=True, exist_ok=True)
    try:
        parent.resolve().relative_to(root_resolved)
    except ValueError as exc:
        raise RuntimeError(f"project target escapes root: {target}") from exc
    return target


def capture_protected_snapshot() -> None:
    PROTECTED_SNAPSHOT.clear()
    missing: list[str] = []
    for rel in PROTECTED_PATHS:
        path = ROOT / rel
        if not path.is_file():
            missing.append(rel)
        else:
            PROTECTED_SNAPSHOT[rel] = path.read_bytes()
    if missing:
        raise RuntimeError(f"missing protected canonical files: {missing}")


def canonical_source_files() -> dict[str, Path]:
    result: dict[str, Path] = {}
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.is_symlink():
            continue
        rel_path = path.relative_to(ROOT)
        rel = rel_path.as_posix()
        if rel in CANONICAL_RUNTIME_FILES or rel == "proof_loop/PAUSE" or rel.startswith("proof_loop/PAUSE."):
            continue
        if any(part in {".git", ".lake", "__pycache__", "proof_loop_runs"} for part in rel_path.parts):
            continue
        result[rel] = path
    return result


def canonical_source_symlinks() -> set[str]:
    """Inventory every non-runtime symlink without following its target."""
    result: set[str] = set()
    for path in ROOT.rglob("*"):
        if not path.is_symlink():
            continue
        rel_path = path.relative_to(ROOT)
        rel = rel_path.as_posix()
        if rel in CANONICAL_RUNTIME_FILES or rel == "proof_loop/PAUSE" or rel.startswith("proof_loop/PAUSE."):
            continue
        if any(part in {".git", ".lake", "__pycache__", "proof_loop_runs"} for part in rel_path.parts):
            continue
        result.add(rel)
    return result


def capture_canonical_tree_snapshot() -> None:
    CANONICAL_TREE_SNAPSHOT.clear()
    symlinks = canonical_source_symlinks()
    if symlinks:
        raise RuntimeError(f"canonical source tree contains symlinks: {sorted(symlinks)}")
    for rel, path in canonical_source_files().items():
        CANONICAL_TREE_SNAPSHOT[rel] = path.read_bytes()


def restore_unexpected_canonical_changes() -> list[str]:
    current = canonical_source_files()
    current_symlinks = canonical_source_symlinks()
    changed = sorted(
        rel for rel in set(current) | set(CANONICAL_TREE_SNAPSHOT) | current_symlinks
        if rel not in current
        or rel not in CANONICAL_TREE_SNAPSHOT
        or current[rel].read_bytes() != CANONICAL_TREE_SNAPSHOT[rel]
    )
    for rel in changed:
        target = ROOT / rel
        if rel not in CANONICAL_TREE_SNAPSHOT:
            if os.path.lexists(target):
                if target.is_dir() and not target.is_symlink():
                    raise RuntimeError(f"refusing to remove unexpected canonical directory: {target}")
                target.unlink()
                fsync_directory(target.parent)
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        fd, temporary = tempfile.mkstemp(prefix=f".{target.name}.", suffix=".tmp", dir=target.parent)
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(CANONICAL_TREE_SNAPSHOT[rel])
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, target)
            fsync_directory(target.parent)
        finally:
            try:
                os.unlink(temporary)
            except FileNotFoundError:
                pass
    return changed


def project_tree_digest(root: Path) -> str:
    """Hash a disposable strategy snapshot, excluding generated caches."""
    import hashlib

    digest = hashlib.sha256()
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root).as_posix()
        if any(part in {".git", ".lake", "__pycache__"} for part in path.relative_to(root).parts):
            continue
        if not path.is_file() or path.is_symlink():
            continue
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def iteration_control_snapshot(iter_dir: Path) -> dict[str, tuple[str, str]]:
    """Fingerprint runner-owned Aristotle controls without following links."""
    snapshot: dict[str, tuple[str, str]] = {}
    for name in ARISTOTLE_CONTROL_NAMES:
        path = iter_dir / name
        if not os.path.lexists(path):
            snapshot[name] = ("missing", "")
        elif path.is_symlink():
            snapshot[name] = ("symlink", os.readlink(path))
        elif path.is_file():
            snapshot[name] = ("file", sha256_file(path))
        elif path.is_dir():
            snapshot[name] = ("directory", "")
        else:
            snapshot[name] = ("special", "")
    return snapshot


def prepare_strategy_snapshot(work_root: Path, iter_dir: Path, stage: str) -> Path:
    """Create a disposable copy so a strategy agent cannot mutate live work."""
    snapshot = iter_dir / f"{stage}_snapshot"
    if snapshot.exists():
        shutil.rmtree(snapshot)

    def ignore(_: str, names: list[str]) -> set[str]:
        ignored = {".git", ".lake", "proof_loop_runs", "__pycache__"}
        return {
            name for name in names
            if name in ignored or name.endswith((".olean", ".ilean", ".pyc"))
        }

    shutil.copytree(work_root, snapshot, ignore=ignore)
    return snapshot


def section_stop_file(stop_file: Path, section: dict[str, Any]) -> Path:
    """Return the soft-pause file for one section.

    With the default global stop file `proof_loop/PAUSE`, section `P4...` is
    paused by `proof_loop/PAUSE.P4...`.  If the caller overrides
    `--stop-file`, the same suffix convention is used next to that file.
    """
    return stop_file.with_name(f"{stop_file.name}.{section['id']}")


def pause_status(args: argparse.Namespace, section: dict[str, Any]) -> dict[str, str] | None:
    """Return pause metadata if the global or section pause file exists."""
    if args.stop_file.exists():
        return {"scope": "global", "file": str(args.stop_file)}
    local_stop = section_stop_file(args.stop_file, section)
    if local_stop.exists():
        return {"scope": "section", "file": str(local_stop)}
    return None


def mark_paused(manifest: dict[str, Any], status: dict[str, str], **extra: Any) -> None:
    manifest["status"] = "paused"
    manifest["paused_at"] = utc_now()
    manifest["pause_scope"] = status["scope"]
    manifest["pause_file"] = status["file"]
    manifest.update(extra)


def load_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def load_sections() -> list[dict[str, Any]]:
    return json.loads(SECTIONS_PATH.read_text(encoding="utf-8"))


def trust_report(root: Path) -> dict[str, Any]:
    cp = subprocess.run(
        ["python3", "scripts/check_trust.py", "--root", str(root), "--json"],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
    )
    try:
        report = json.loads(cp.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"trust audit did not return JSON: {cp.stdout}") from exc
    if not isinstance(report, dict):
        raise RuntimeError("trust audit returned a non-object")
    return report


def count_sorries_at(root: Path) -> int:
    report = trust_report(root)
    return len(report.get("external_sorries", [])) + len(report.get("internal_sorries", []))


def count_section_sorries_at(root: Path, section: dict[str, Any]) -> int:
    del section
    return count_sorries_at(root)


def rel_file_block(root: Path, paths: list[str], max_each: int = 50000) -> str:
    chunks: list[str] = []
    for rel in paths:
        path = root / rel
        suffix = "lean" if path.suffix == ".lean" else "text"
        chunks.append(f"\n\n## FILE: {rel}\n\n```{suffix}\n")
        chunks.append(read_text(path, max_each).strip())
        chunks.append("\n```\n")
    return "".join(chunks)


def latest_file(pattern_root: Path, glob: str) -> Path | None:
    files = sorted(pattern_root.glob(glob), key=lambda p: p.stat().st_mtime if p.exists() else 0)
    return files[-1] if files else None


def collect_context(section: dict[str, Any], root: Path) -> str:
    coverage = read_text(root / "COVERAGE.md", 20000)
    readme = read_text(root / "README.md", 8000)
    if section.get("workflow") == "polish":
        target_files = "\n".join(f"- `{path}`" for path in section.get("files", []))
        polish_plan = read_text(root / "POLISHING_28_PLAN.md", 30000)
        return f"""
# Repository Context

Current worktree root: `{root}`

The project is complete and sorry-free at the baseline. Use `COVERAGE.md` to
identify public declarations, but inspect exact proof bodies directly in the
worktree instead of relying on copied source excerpts.

## Primary polishing files

{target_files}

## Strict polishing plan

```markdown
{polish_plan.strip()}
```

## COVERAGE.md

```markdown
{coverage.strip()}
```

## README.md

```markdown
{readme.strip()}
```
"""

    plan_rel = section.get("plan_file", "PLAN.md")
    source_rel = section.get("source_file", "proof_loop/SOURCE.tex")
    prior_rel = section.get("prior_artifacts_file")
    plan = read_text(root / plan_rel, 60000)
    source = read_text(root / source_rel, 100000)
    prior_aristotle = (
        read_text(root / prior_rel, 20000) if prior_rel else "(no prior Aristotle artifacts)"
    )
    context_files = [str(path) for path in section.get("context_files", [])]
    context_block = rel_file_block(root, context_files) if context_files else "(none)"
    conventions = section.get(
        "conventions",
        "Follow the existing repository APIs and Mathlib style. Put reusable "
        "computability infrastructure in a foundation module only when its "
        "generality is demonstrated by more than one downstream use.",
    )
    return f"""
# Repository Context

Current worktree root: `{root}`

Read `COVERAGE.md` first and build on the declarations named there. Do not
re-prove an existing result under a chapter-specific name.

Conventions: {conventions}

## COVERAGE.md

```markdown
{coverage.strip()}
```

## README.md

```markdown
{readme.strip()}
```

## Prior Aristotle artifacts

```markdown
{prior_aristotle.strip()}
```

## Formalization plan (`{plan_rel}`)

```markdown
{plan.strip()}
```

## Primary source (`{source_rel}`, verbatim excerpt)

```tex
{source.strip()}
```

# Read-only reference files
{context_block}
"""


def scan_sorries() -> str:
    return scan_sorries_at(ROOT)


def scan_section_sorries_at(root: Path, section: dict[str, Any]) -> str:
    del section
    report = trust_report(root)
    internal = report.get("internal_sorries", [])
    external = report.get("external_sorries", [])
    chunks = ["ACTIONABLE EXTERNAL PROOF BODIES (the global objective):"]
    chunks.extend(f"  {item}" for item in external)
    if not external:
        chunks.append("  (none)")
    chunks.append("ACTIONABLE SUPPORTING INTERNAL HOLES:")
    if internal:
        chunks.extend(f"  {item}" for item in internal)
    else:
        chunks.append("  (none)")
    if report.get("errors"):
        chunks.append("TRUST AUDIT ERRORS:")
        chunks.extend(f"  {item}" for item in report["errors"])
    return "\n".join(chunks)


def scan_sorries_at(root: Path) -> str:
    return scan_section_sorries_at(root, {})


def is_polishing(section: dict[str, Any]) -> bool:
    return section.get("workflow") == "polish"


def scan_polish_debt_at(root: Path) -> str:
    """Return static proof-engineering debt that agents can attack locally."""
    needles = (
        "set_option maxHeartbeats",
        "set_option maxRecDepth",
        "set_option linter.",
    )
    lines: list[str] = []
    source_root = root / "KolmogorovMathlib"
    for path in sorted(source_root.rglob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        rel = path.relative_to(root)
        for idx, line in enumerate(text.splitlines(), 1):
            stripped = line.strip()
            if any(needle in line for needle in needles) or stripped == "import Mathlib":
                lines.append(f"{rel}:{idx}:{line}")
    lakefile = root / "lakefile.toml"
    if lakefile.exists():
        for idx, line in enumerate(lakefile.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            if re.search(r"(?:weak\.)?linter\..*=\s*false\b", line):
                lines.append(f"lakefile.toml:{idx}:{line}")
    tactic_patterns = {
        "simp_all": r"\bsimp_all\b",
        "aesop": r"\baesop\b",
        "grind": r"\bgrind\b",
        "nlinarith": r"\bnlinarith\b",
    }
    counts = {name: 0 for name in tactic_patterns}
    for path in sorted(source_root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        for name, pattern in tactic_patterns.items():
            counts[name] += len(re.findall(pattern, text))
    lines.append(
        "TACTIC CANDIDATE INVENTORY (review contextually; not an automatic ban): "
        + ", ".join(f"{name}={count}" for name, count in counts.items())
    )
    return "\n".join(lines) if lines else "(no static polishing debt found)"


def import_pipeline_module():
    os.environ.setdefault("HARPER_LAB_ROOT", str(ROOT))
    scripts_dir = DEFAULT_STABILITY_LAB_ROOT / "scripts"
    if str(scripts_dir) not in sys.path:
        sys.path.insert(0, str(scripts_dir))
    import harper_pipeline  # type: ignore

    return harper_pipeline


def import_pipeline():
    return import_pipeline_module().call_agent_safe


def production_preflight(args: argparse.Namespace) -> dict[str, Any]:
    """Validate the pinned, non-billed conveyor dependencies before a run."""
    recovery = recover_incomplete_merge()
    if not args.dry_run and not args.submit_aristotle:
        raise RuntimeError(
            "production mode requires --submit-aristotle; use --dry-run for packet-only validation"
        )
    hp = import_pipeline_module()
    actual_agy = Path(hp.AGY_BIN).resolve()
    if actual_agy != EXPECTED_AGY_BIN.resolve():
        raise RuntimeError(f"unexpected agy binary: {actual_agy}")
    for binary in (EXPECTED_AGY_BIN, ARISTOTLE_BIN):
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise RuntimeError(f"missing or non-executable conveyor dependency: {binary}")

    checks: dict[str, Any] = {"merge_recovery": recovery}
    raw_outputs: dict[str, str] = {}
    for name, command in (
        ("agy_version", [str(EXPECTED_AGY_BIN), "--version"]),
        ("agy_models", [str(EXPECTED_AGY_BIN), "models"]),
        ("aristotle_version", [str(ARISTOTLE_BIN), "--version"]),
    ):
        rc, output = command_output(command, ROOT, timeout=120)
        raw_outputs[name] = output
        checks[name] = {"returncode": rc, "output": output[:4000]}
        if rc != 0:
            raise RuntimeError(f"preflight command failed: {' '.join(command)}\n{output}")
    if GEMINI_MODEL not in raw_outputs["agy_models"]:
        raise RuntimeError(f"agy does not expose pinned model {GEMINI_MODEL}")
    if CLAUDE_MODEL not in raw_outputs["agy_models"]:
        raise RuntimeError(f"agy does not expose pinned model {CLAUDE_MODEL}")

    trust_rc, trust_output = command_output(
        ["python3", str(ROOT / "scripts/check_trust.py"), "--root", str(ROOT)],
        ROOT,
        timeout=180,
    )
    checks["canonical_trust"] = {"returncode": trust_rc, "output": trust_output}
    if trust_rc != 0:
        raise RuntimeError(f"canonical trust preflight failed:\n{trust_output}")
    dependency_rc, dependency_output = command_output(
        ["python3", str(ROOT / "scripts/check_dependencies.py"), "--root", str(ROOT)],
        ROOT,
        timeout=300,
    )
    checks["canonical_dependencies"] = {
        "returncode": dependency_rc,
        "output": dependency_output,
    }
    if dependency_rc != 0:
        raise RuntimeError(f"canonical dependency preflight failed:\n{dependency_output}")
    return checks


def previous_outputs(iter_dir: Path) -> str:
    chunks: list[str] = []
    for path in sorted(iter_dir.glob("*.md")):
        if path.name.endswith(".prompt.md") or path.name == "aristotle_prompt.md":
            continue
        chunks.append(f"\n\n# PREVIOUS OUTPUT: {path.name}\n\n")
        chunks.append(read_text(path, 50000).strip())
        chunks.append("\n")
    return "".join(chunks).strip() or "(none yet)"


def latest_strategy_outputs(section_dir: Path, before_iteration: int) -> str:
    strategy_dirs: list[Path] = []
    for path in section_dir.glob("iter_*_strategy"):
        try:
            iteration = int(path.name.split("_", 2)[1])
        except Exception:
            continue
        if iteration < before_iteration:
            strategy_dirs.append(path)
    if not strategy_dirs:
        return "(no previous strategy iteration for this section)"
    latest = sorted(strategy_dirs, key=lambda p: p.name)[-1]
    chunks = [f"# LATEST STRATEGY: {latest.name}\n"]
    for name in ["07_aristotle.md", "02_opus.md", "01_gemini.md"]:
        path = latest / name
        if path.exists():
            chunks.append(f"\n\n## {name}\n\n")
            chunks.append(read_text(path, 50000).strip())
    aristotle_log = latest / "aristotle_submit.log"
    if aristotle_log.exists():
        tail = "\n".join(read_text(aristotle_log, 50000).splitlines()[-80:])
        chunks.append("\n\n## Aristotle strategy log tail\n\n```text\n")
        chunks.append(tail)
        chunks.append("\n```\n")
    return "".join(chunks).strip()


def latest_repair_context(section_dir: Path, before_iteration: int) -> str:
    """Return the most recent failed verification for the next repair agent.

    A rejected stage or merge is ordinary proof-search feedback, not a reason to
    stop the conveyor.  The worktree is deliberately preserved, so the next
    iteration also needs the corresponding diagnostic rather than having to
    rediscover it from scratch.
    """
    prior: list[tuple[int, Path]] = []
    for path in section_dir.glob("iter_*"):
        try:
            iteration = int(path.name.split("_", 2)[1])
        except (IndexError, ValueError):
            continue
        if iteration < before_iteration:
            prior.append((iteration, path))
    for _iteration, path in sorted(prior, reverse=True):
        manifest = load_json(path / "manifest.json", {})
        stages = manifest.get("stages", [])
        stage_failed = any(
            isinstance(stage, dict)
            and (
                stage.get("ok") is False
                or int(stage.get("trust_rc", 0) or 0) != 0
                or int(stage.get("audit_rc", 0) or 0) != 0
            )
            for stage in stages
        )
        merge = manifest.get("merge_gate", {})
        merge_status = merge.get("status") if isinstance(merge, dict) else None
        merge_failed = merge_status not in {None, "ACCEPTED", "NO_CHANGES"}
        status = str(manifest.get("status", ""))
        iteration_failed = stage_failed or merge_failed or status.startswith("blocked_")
        if not iteration_failed:
            continue
        chunks = [
            f"Most recent repair target: `{path.name}`\n\n",
            "```json\n",
            json.dumps(manifest, indent=2, sort_keys=True)[-16000:],
            "\n```\n",
        ]
        diagnostic_paths = sorted(path.glob("*.audit.md"))
        merge_audit = path / "merge_gate" / "audit.log"
        if merge_audit.exists():
            diagnostic_paths.append(merge_audit)
        for diagnostic in diagnostic_paths[-3:]:
            chunks.extend([
                f"\n## {diagnostic.relative_to(path)} (tail)\n\n```text\n",
                read_text(diagnostic, 30000)[-12000:],
                "\n```\n",
            ])
        return "".join(chunks)
    return "(no unresolved verification failure from an earlier iteration)"


def section_header(section: dict[str, Any]) -> str:
    return f"""
# Section

- id: `{section['id']}`
- title: {section['title']}
- module: `{section['module']}`
- targets: {', '.join(f'`{t}`' for t in section.get('targets', []))}
- notes: {section.get('notes', '')}
"""


def polishing_ordinary_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    work_root: Path,
) -> str:
    role = {
        "01_gemini": "Gemini, proof-polishing implementer",
        "02_opus": "Opus, final verifier, repairer, and Aristotle-packet curator",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Follow the latest strategy's exact ownership batch. Remove strict-linter "
            "warnings and locally justified proof debt without changing declarations or "
            "executable definitions. Run direct strict-linter checks for every touched file."
        ),
        "02_opus": (
            "Adversarially review Gemini's actual diff. Revert regressions, repair and "
            "continue the same small batch where safe, then run direct strict-linter and "
            "affected checks. The deterministic merge gate will run the full audit, so "
            "do not duplicate it inside the agent stage. Confirm that theorem statements "
            "and assumptions are unchanged, and curate exact remaining leaves for "
            "Aristotle. If every stop "
            "condition in the polishing plan is independently satisfied, create the "
            "section completion marker; otherwise leave it absent."
        ),
    }[stage]
    completion_file = section.get("completion_file", "")
    completion_rule = (
        f"Only Opus may create `{completion_file}`, after independently verifying every "
        "completion gate in `POLISHING_28_PLAN.md`, finding no remaining safe, "
        "evidence-backed improvement, and confirming that the latest strategic Opus "
        "and Aristotle reviews both returned `NO_SAFE_IMPROVEMENT`."
        if completion_file
        else "Do not declare the section complete without satisfying every plan gate."
    )
    return f"""
You are {role} in a Lean 4 post-proof polishing iteration.

Iteration: {iteration}. This is an ordinary editing iteration.
Worktree: `{work_root}`

The entire Lean 4.28 formalization is already complete and kernel-checked.
This iteration must improve implementation quality without changing its
mathematical content. Do not add new milestones or draft new theorems.

{section_header(section)}

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Current `sorry` scan (must remain empty)

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Latest strategic polishing plan

```markdown
{latest_strategy_outputs(work_root.parent, iteration)}
```

# Task

{stage_task}

Priorities, in order:
1. Eliminate all warnings revealed by `flexible`, `longLine`, `multiGoal`, and
   `openClassical`; remove their `lakefile.toml` suppressions only when the
   whole direct-file sweep is clean.
2. Keep zero heartbeat/recursion overrides, Lean warnings, source-level linter
   suppressions, broad imports, and temporary measurement scaffolding.
3. Narrow imports, remove genuinely dead private helpers and stale process
   commentary, and preserve useful mathematical documentation.
4. Prefer short robust Mathlib-style structural proofs. Treat broad `simp_all`,
   `aesop`, `grind`, and `nlinarith` as review candidates, not automatic bans.

Use targeted `lake env lean <file>` or affected module builds while editing. Do not
launch a blind full build inside an agent stage. The deterministic local merge gate
runs `bash scripts/audit.sh` once for a stable local candidate; it runs again only
when Aristotle returns additional changes that require a fresh gate.

Completion rule: {completion_rule}

Required output:

STATUS: IMPROVED / NO_SAFE_IMPROVEMENT / BUILD_BROKEN / INTERFACE_PROBLEM

## Changes Made
List exact files/declarations and the debt removed.

## Verification
Report direct strict-linter checks, targeted builds, full audit if run, and
the exact remaining warning/suppression counts.

## Aristotle Optimization Packet
Give 1-3 exact expensive declarations or style leaves for Aristotle. Include
the existing proof and any tested partial replacement; never create a `sorry`.

## Risks
Report compile-time regressions, statement drift, or reverted attempts.

Hard constraints:
- Zero `sorry`/`sorryAx` before and after every stage.
- No `axiom`, `admit`, `unsafe`, `implemented_by`, or `native_decide`.
- Do not change theorem statements, assumptions, definitions' semantics, or public names.
- Never replace a heartbeat override by a larger/global override or by disabling limits.
- Never add or relocate a linter suppression. Preserve executable definition bodies.
- If an attempted cleanup does not compile, revert that attempt before finishing.
- Do not commit, push, or edit files outside the allowed section prefixes.

{context}
"""


def ordinary_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    work_root: Path,
) -> str:
    if is_polishing(section):
        return polishing_ordinary_prompt(stage, section, iteration, context, previous, work_root)
    role = {
        "01_gemini": "Gemini, implementation agent",
        "02_opus": "Opus, final verifier, repairer, and Aristotle-packet preparer",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Inspect the current Lean tree first, then implement the highest-priority "
            "unfinished work that advances the global goal. The latest strategy is a "
            "rolling dependency map, not an iteration assignment. Skip items already "
            "completed, and if you finish the suggested item early, continue to the "
            "next sound dependency in the same turn. Never produce an empty iteration "
            "merely because a strategy item is already complete. If a target is too "
            "hard, isolate smaller named lemmas and keep progressing toward the main "
            "internal theorem."
        ),
        "02_opus": (
            "Perform the final adversarial review of Gemini's edits. Keep correct "
            "progress, reject or repair unsound shortcuts and build failures, close "
            "additional leaves where possible, and then continue with the next "
            "unfinished dependency if Gemini completed its initial target. Treat the "
            "latest strategy as revisable guidance rather than a fixed batch. Run "
            "targeted builds plus the full audit as far as practical, and curate the "
            "best remaining exact obligations for Aristotle."
        ),
    }[stage]
    global_goal = section.get(
        "global_goal",
        "Formalize the complete source section described by the section plan.",
    )
    milestone_guidance = section.get(
        "milestone_guidance",
        "Follow the plan in dependency order. If the current milestone is closed, "
        "advance to the next incomplete milestone.",
    )
    statement_guards = section.get(
        "statement_guards",
        "Quantify uniform slack constants before varying objects; never weaken an "
        "already accepted theorem; validate definitions on boundary cases.",
    )
    completion_file = section.get("completion_file", "")
    completion_rule = (
        f"Only the final Opus may create `{completion_file}`, and only after every "
        "plan milestone is represented by kernel-checked public declarations, the "
        "section has no `sorry`, and the full audit passes."
        if completion_file
        else "Do not declare the whole section complete unless every plan milestone is closed."
    )
    return f"""
You are {role} for a Lean 4 proof implementation iteration.

Iteration: {iteration}

This is an ordinary proof iteration, not the strategic planning iteration.
You may edit files in the isolated worktree below.

GLOBAL GOAL: {global_goal}

Closing current `sorry`s is only the local step. {milestone_guidance}
New statements may contain honest, precisely isolated `sorry` leaves while
being drafted, but they must preserve the exact mathematical content of the
source rather than replacing asymptotic claims by tautological interfaces.

Statement quality gates: {statement_guards}

Completion rule: {completion_rule}

Worktree: `{work_root}`

The checksum-frozen files `AllenderOQ3/Model.lean`,
`AllenderOQ3/Incidence.lean`, `AllenderOQ3/Principles.lean`, and
`AllenderOQ3/Statement.lean` must not be edited.  The two proof bodies in
`ExternalFacts.lean` are actionable and are the global objective. Supporting
lemmas belong under `AllenderOQ3/Internal`. If a frozen signature is genuinely wrong,
stop and report `INTERFACE_PROBLEM` with a counterexample.

{section_header(section)}

# Current `sorry` scan in this worktree

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Most recent unresolved build/audit failure

```markdown
{latest_repair_context(work_root.parent, iteration)}
```

If this section contains a failure, repair it first.  Once the build/audit is
green, continue immediately with the next unfinished dependency; a repair-only
turn should not become an empty turn when time remains.

# Latest strategic plan for this section

```markdown
{latest_strategy_outputs(work_root.parent, iteration)}
```

Adaptive execution rule: the strategy above is not a schedule and does not own
specific future iteration numbers. Re-check the actual Lean tree and sorry scan.
Skip every item already proved, continue past an item completed early, and use the
global goal as the fallback whenever the strategy backlog is exhausted or stale.
An ordinary iteration must never be empty solely because the previous strategy's
concrete suggestions have already been completed.

# Task

{stage_task}

Required output:

STATUS: IMPLEMENTED / PARTIAL_IMPLEMENTATION / BUILD_BROKEN / BLOCKED_BY_MATH / INTERFACE_PROBLEM

## Changes Made
List exact files and declarations changed.

## Verification
Say whether you ran `lake build`, `bash scripts/audit.sh`, or targeted
`lake env lean ...`; include the relevant result.

## Remaining Sorries
List exact declarations still open in this section and why they are now smaller
or better isolated.

## Aristotle Leaf Packet
State 1-3 remaining leaf obligations that are small enough for Aristotle.
Include theorem statements in Lean-like syntax when possible.

## Risks
List any questionable edits, false shortcuts avoided, or places needing review.

Hard constraints:
- No `axiom`, `constant`, `opaque`, `admit`, `unsafe`, or `implemented_by`.
- Close the two exact external proof bodies without changing their frozen principle
  types. Do not move a `sorry` unless the replacement obligations are strictly
  smaller or more standard and their dependency is recorded.
- Do not weaken theorem statements.
- Do not edit any checksum-frozen file; report `INTERFACE_PROBLEM` instead.
- Preserve module boundaries: this section may use interface statements from
  other sections only as hypotheses unless the dependency graph already permits
  the import.

{context}
"""


def polishing_strategy_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    previous: str,
    span: int,
    work_root: Path,
) -> str:
    role = {
        "01_gemini": "Gemini polishing strategist",
        "02_opus": "Opus independent critic and final polishing-plan synthesizer",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Measure all four enabled-linter warning classes and the architecture "
            "baseline: import graph, reverse-dependency fan-out, module sizes, "
            "elaboration/build hotspots, and the cost of validating a local change."
        ),
        "02_opus": (
            "Independently re-measure Gemini's claims against the actual declarations, "
            "imports, and build hotspots. Reject local metric gaming and synthesize the "
            "final executable four-iteration plan with exact files, declarations, "
            "acceptance tests, and rollback criteria."
        ),
    }[stage]
    return f"""
You are {role} for strategic Lean proof polishing.

Iteration: {iteration}. Plan the next {span} ordinary iterations. Do not edit
the worktree during this strategy iteration.

{section_header(section)}

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Current `sorry` scan (must remain empty)

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous strategy-agent outputs

```markdown
{previous}
```

# Long-term scalability objective

Assume this library will grow by at least 10x and plausibly 100x. Optimize
whole-project maintainability, elaboration time, rebuild fan-out, and review
cost rather than tactic counts or local line count. Treat zero warnings as a
baseline, not the end state. Measure the actual import graph and build
hotspots before proposing module splits or infrastructure. A strategy should
include at least one concrete architecture or layered-build improvement when
the measurements justify it. Fast affected checks may supplement the full
audit, but the full root audit remains the release gate and must never be
weakened.

# Stage-specific task

{stage_task}

Required output:

STATUS: STRATEGY_READY / NO_SAFE_IMPROVEMENT / NEEDS_HUMAN_DECISION

## 10x-100x Scalability Assessment
Report the measured import/fan-out, module-size, elaboration/build, and
change-validation bottlenecks. Distinguish present evidence from speculation.

## Best Plan For The Next Four Ordinary Iterations
For each iteration give exclusive file ownership, exact warning counts and
declarations or infrastructure artifacts, proposed cleanup, scalability
impact, the fastest sound affected-check gate, direct strict-linter
verification, full-build gate, and rollback criterion. Re-measure from the
actual Lean 4.28 worktree.

## Aristotle Optimization Priority
Rank 3-8 exact proof or architecture leaves where independent work could reduce
elaboration/rebuild cost, improve module boundaries, remove a local heartbeat
override, or replace a brittle proof without changing the public API.

## Risks
Flag any proposal that could alter the API, assumptions, semantics, or compile time.

Hard constraints: no edits, no new `sorry`, no theorem weakening, no mechanical
tactic-count reduction, no speculative file splitting without measured
dependency benefit, and no plan whose only effect is moving or increasing a
resource override. Do not weaken the final full-project audit.
"""


def strategy_prompt(
    stage: str,
    section: dict[str, Any],
    iteration: int,
    context: str,
    previous: str,
    span: int,
    work_root: Path,
) -> str:
    if is_polishing(section):
        return polishing_strategy_prompt(stage, section, iteration, previous, span, work_root)
    role = {
        "01_gemini": "Gemini strategy planner",
        "02_opus": "Opus independent critic and final strategy synthesizer",
    }[stage]
    stage_task = {
        "01_gemini": (
            "Reassess the whole proof from the actual declarations and dependency "
            "graph. Produce a rolling priority map: invariants, dependency order, best "
            "next moves, alternatives when a route stalls, and criteria for advancing. "
            "Identify concrete Lean-sized leaves, but do not assign them to fixed future "
            "iteration numbers."
        ),
        "02_opus": (
            "Independently critique Gemini's plan against the current Lean code, correct "
            "false assumptions and missing dependencies, and synthesize a durable "
            "rolling strategy with ordered priorities and exact Aristotle-sized leaves. "
            "It must remain useful when ordinary agents complete several leaves faster "
            "than expected; never turn it into a fixed iteration schedule."
        ),
    }[stage]
    global_goal = section.get(
        "global_goal",
        "Formalize the complete source section described by the section plan.",
    )
    milestone_guidance = section.get(
        "milestone_guidance",
        "Follow the plan in dependency order and advance after closing a milestone.",
    )
    statement_guards = section.get(
        "statement_guards",
        "Do not weaken asymptotic or uniform claims, and validate all new definitions "
        "against boundary cases and existing interfaces.",
    )
    return f"""
You are {role} for a strategic Lean proof-planning iteration.

Iteration: {iteration}. This is a strategy iteration. Do not try to solve a
single proof and do not allocate exact tasks to fixed future iteration numbers.
Maintain the rolling strategy for reaching the global goal. Ordinary iterations
will consult it, skip completed work, and continue beyond its concrete examples.

{section_header(section)}

# Current `sorry` scan in this section worktree

```text
{scan_section_sorries_at(work_root, section)}
```

# Previous outputs in this iteration

```markdown
{previous}
```

# Stage-specific task

{stage_task}

Required output:

STATUS: STRATEGY_READY / NEEDS_HUMAN_DECISION / INTERFACE_PROBLEM

GLOBAL GOAL: {global_goal}

Milestone policy: {milestone_guidance}

Statement quality gates: {statement_guards}

## Section Diagnosis
What is the real dependency shape of this section (relative to the global plan)?

## Ordered Strategic Backlog
Give a dependency-aware priority order of currently useful targets. For each,
state the proof idea, prerequisites, Aristotle-sized leaves, and evidence that
the target is still unfinished. Do not attach targets to iteration numbers.

## Adaptive Execution And Pivot Rules
Explain how ordinary agents should choose the next target, what to do when a
target is completed earlier than expected, how to bypass stale plan items, and
which alternative route to take when the preferred route stalls.

## Parallelization Notes
Which subtargets can be worked independently?

## Global Completion Criterion
The objective is to eliminate both external proof holes and every temporary
supporting hole. The final unconditional theorem must be free of `sorryAx`.
State any additional kernel/audit conditions needed before declaring success.

## Stop Conditions
Pause only for a genuine interface contradiction, a mathematical blocker that
survives reasonable alternative routes, or a need for user authority.

Hard constraints:
- No interface weakening.
- Do not edit the worktree on a strategy iteration.
- Treat the two remaining external theorem bodies as the goal; preserve their
  checksum-frozen proposition types.
- No hidden dependency on unproved worker proofs except through explicit
  statement hypotheses.
- Prefer small leaf lemmas with stable Lean statements.

{context}
"""


def write_aristotle_packet(
    section: dict[str, Any],
    iteration: int,
    iter_dir: Path,
    mode: str,
    work_root: Path,
) -> Path:
    project_label = f"AllenderOQ3_{section['id']}_iter{iteration:03d}_{mode}"
    if is_polishing(section) and mode == "strategy":
        prompt = f"""
You are Aristotle reviewing a strategic Lean 4 proof-polishing iteration.

Project label: `{project_label}`
The submitted project is a disposable copy.  Work only in the current project
directory exposed by Aristotle; do not use any absolute path from the prompt.
Section: `{section['id']}` / {section['title']}

Do not edit proofs in this strategic round. Review the two local agents' plans and
produce the safest next-four-iteration optimization plan. The existing theorem
statements and semantics are frozen.

Begin with exactly one of:

`STATUS: STRATEGY_READY`

`STATUS: NO_SAFE_IMPROVEMENT`

`STATUS: NEEDS_HUMAN_DECISION`

Use `NO_SAFE_IMPROVEMENT` only after independently checking every completion gate
in `POLISHING_28_PLAN.md`; zero warnings alone is insufficient.

Assume the library will grow by 10x and may grow by 100x. Review not only local
proof style but also the measured import graph, reverse-dependency fan-out,
module boundaries, elaboration/build hotspots, and layered validation
workflow. Prefer changes that keep local edits cheap to validate at that scale.
Fast affected checks may supplement, but never replace or weaken, the final
full-project audit.

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Strategy agent outputs

```markdown
{previous_outputs(iter_dir)}
```

Rank exact proof and architecture leaves where a cheaper equivalent proof,
cleaner module boundary, or lower rebuild fan-out is plausible. State targeted
affected checks, full-build checks, and rollback criteria. Never propose
adding, moving, or increasing a heartbeat override.
"""
    elif is_polishing(section):
        prompt = f"""
You are Aristotle optimizing an already-complete Lean 4 formalization.

Project label: `{project_label}`
The submitted project is a disposable copy.  Work only in the current project
directory exposed by Aristotle; do not use any absolute path from the prompt.
Section: `{section['id']}` / {section['title']}

The project currently builds with zero `sorry`. Improve one or more exact
proofs selected by the previous agents: remove a local heartbeat override,
reduce elaboration cost, resolve an info/warning, or replace a brittle tactic
script with a robust Mathlib-style proof. Edit the submitted project and return
all useful partial work even if every optimization does not succeed.

Hard constraints:
- Keep every theorem statement, assumption, public name, and definition's semantics unchanged.
- Keep the project free of `sorry`, `sorryAx`, `axiom`, `admit`, `unsafe`,
  `implemented_by`, and `native_decide`.
- Never raise, globalize, disable, or merely relocate a resource limit.
- Revert any attempted edit that does not compile.

# Current static polishing debt

```text
{scan_polish_debt_at(work_root)}
```

# Agent outputs and exact optimization packet

```markdown
{previous_outputs(iter_dir)}
```
"""
    elif mode == "strategy":
        prompt = f"""
You are Aristotle working on strategic proof planning for a Lean 4 project.

Project label: `{project_label}`
The submitted project is a disposable copy.  Work only in the current project
directory exposed by Aristotle; do not use any absolute path from the prompt.
Section: `{section['id']}` / {section['title']}
Module: `{section['module']}`

This is strategy iteration {iteration}. Do not try to solve a large proof in
one shot. Review both preceding strategy agents and produce a rolling strategic
map for this section, with leaf obligations suitable for future Aristotle
submissions. Do not assign work to fixed future iteration numbers: ordinary
iterations may close several targets at once and must then continue toward the
global theorem rather than making empty calls.

The two remaining `sorry`s in `AllenderOQ3/ExternalFacts.lean` are the main
proof targets; rotation-zero attainment is kernel-proved. Never weaken their
types. The four frozen API
files named in `proof_loop/frozen_api.sha256` are read-only.

Required output:

STATUS: STRATEGY_READY / NEEDS_HUMAN_DECISION / INTERFACE_PROBLEM

## Ordered Strategic Backlog
Give dependency-ordered targets, exact Lean files when known, mathematical
proof ideas, prerequisites, and Aristotle-sized leaves. This is a priority map,
not an iteration schedule.

## Adaptive Execution And Pivot Rules
State how later agents skip completed targets, continue when work finishes
early, revise stale priorities, and fall back to the overall objective.

## Global Completion Criterion
Prove the Hansen and quantitative ACC facts, preserve the already sorry-free
conditional theorem, and include the required build and trust checks. Completion
requires the unconditional theorem to have no `sorryAx`.

## Aristotle Leaf Priority
Rank the 3-8 leaf obligations that Aristotle should attack first.

## Risks
Name any statement that looks too large, too vague, or badly shaped for
Aristotle.

# Current `sorry` scan

```text
{scan_section_sorries_at(work_root, section)}
```

# Strategy agent outputs

```markdown
{previous_outputs(iter_dir)}
```
"""
    else:
        prompt = f"""
You are Aristotle working on a Lean 4 project.

Project label: `{project_label}`
The submitted project is a disposable copy.  Work only in the current project
directory exposed by Aristotle; do not use any absolute path from the prompt.
Section: `{section['id']}` / {section['title']}
Module: `{section['module']}`

The previous agents selected leaf proof targets. Use the context below and try
to prove one or more small Lean obligations without changing the frozen theorem
statements.

 Hard constraints:
- No `axiom`, `constant`, `opaque`, `admit`, `unsafe`, or `implemented_by`.
- Do not weaken existing statements.
- Do not edit any file listed in `proof_loop/frozen_api.sha256`.
- The two external `sorry`s are actionable. Prove them through exact supporting
  lemmas without changing the frozen proposition types.
- Prefer proving leaf lemmas exactly as stated or curated by Opus in
  `02_opus.md`.

# Current `sorry` scan

```text
{scan_section_sorries_at(work_root, section)}
```

# Opus curation

Gemini's transcript is intentionally omitted here. Opus has already checked
and distilled it into the actionable leaf packet below.

```markdown
{read_text(iter_dir / "02_opus.md", 20000)}
```
"""
    prompt_path = iter_dir / "aristotle_prompt.md"
    write_text(prompt_path, textwrap.dedent(prompt).strip() + "\n")
    submit = f"""#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess

source_dir = Path({str(work_root)!r})
project_label = {project_label!r}
project_dir = Path({str(iter_dir / project_label)!r})
prompt = Path({str(prompt_path)!r}).read_text(encoding="utf-8")

def ignore(_dir, names):
    ignored = {{
        ".git",
        ".lake",
        "proof_loop_runs",
        "proof_loop_readiness",
        "interface_part_reviews",
        "reviews",
        "__pycache__",
    }}
    return {{
        name for name in names
        if name in ignored or name.endswith(".olean") or name.endswith(".ilean") or name.endswith(".pyc")
    }}

if project_dir.exists():
    shutil.rmtree(project_dir)
shutil.copytree(source_dir, project_dir, ignore=ignore)
(project_dir / "ARISTOTLE_PROJECT_LABEL.md").write_text(
    f"# {{project_label}}\\n\\nThis is an Aristotle submission copy for section `{section['id']}`, "
    f"iteration `{iteration}`, mode `{mode}`.\\n",
    encoding="utf-8",
)

cmd = [
    {str(ARISTOTLE_BIN)!r},
    "submit",
    prompt,
    "--project-dir",
    str(project_dir),
]
print("project_label:", project_label, flush=True)
print("command:", " ".join(cmd[:2] + ["<prompt>", "--project-dir", str(project_dir)]), flush=True)
raise SystemExit(subprocess.run(cmd).returncode)
"""
    submit_path = iter_dir / "submit_aristotle.py"
    write_text(submit_path, submit)
    return prompt_path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_aristotle_archive(archive: Path, iter_dir: Path) -> dict[str, Any]:
    """Validate provenance-independent tar safety before accepting a download."""
    if archive.is_symlink() or not archive.is_file():
        raise RuntimeError(f"Aristotle archive is not a regular file: {archive}")
    validation_dir = iter_dir / "aristotle_archive_validation"
    try:
        project = safe_extract_project_tar(archive, validation_dir)
        if project is None:
            raise RuntimeError("Aristotle archive contains no Lean project")
        return {
            "archive_sha256": sha256_file(archive),
            "archive_bytes": archive.stat().st_size,
        }
    finally:
        if validation_dir.exists():
            shutil.rmtree(validation_dir)


def read_existing_aristotle_state(state_path: Path) -> tuple[dict[str, Any] | None, str | None]:
    """Missing is fresh; every malformed existing state is fail-closed."""
    if not os.path.lexists(state_path):
        return {}, None
    if state_path.is_symlink() or not state_path.is_file():
        return None, "state_is_not_a_regular_file"
    try:
        value = json.loads(state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None, "state_is_not_valid_json"
    if not isinstance(value, dict) or not value:
        return None, "state_is_not_a_nonempty_object"
    project_id = value.get("project_id")
    task_id = value.get("task_id")
    recognized = (
        value.get("automatic_resubmit_forbidden") is True
        or (
            isinstance(project_id, str)
            and bool(project_id.strip())
            and (task_id is None or (isinstance(task_id, str) and bool(task_id.strip())))
        )
    )
    if not recognized:
        return None, "state_has_no_recognized_submission_schema"
    return value, None


def submit_aristotle(iter_dir: Path, timeout_seconds: int) -> dict[str, Any]:
    script = iter_dir / "submit_aristotle.py"
    if not script.exists():
        return {"submitted": False, "reason": "missing submit_aristotle.py"}
    attempts: list[tuple[int, subprocess.CompletedProcess[str]]] = []
    archive = iter_dir / "aristotle_result.tar.gz"
    state_path = iter_dir / "aristotle_state.json"
    previous_state, state_error = read_existing_aristotle_state(state_path)
    if state_error is not None:
        return {
            "submitted": True,
            "resumed": True,
            "returncode": 1,
            "reason": "ambiguous_aristotle_submission_without_id",
            "state_error": state_error,
            "automatic_resubmit_forbidden": True,
        }
    assert previous_state is not None
    if os.path.lexists(archive):
        try:
            metadata = validate_aristotle_archive(archive, iter_dir)
        except Exception as exc:
            return {
                "submitted": True,
                "resumed": True,
                "returncode": 1,
                "reason": "untrusted_preexisting_aristotle_archive",
                "archive_error": f"{type(exc).__name__}: {exc}",
            }
        provenance_ok = (
            bool(previous_state.get("project_id"))
            and bool(previous_state.get("task_id"))
            and previous_state.get("archive_project_id") == previous_state.get("project_id")
            and previous_state.get("archive_task_id") == previous_state.get("task_id")
            and previous_state.get("archive_sha256") == metadata["archive_sha256"]
            and previous_state.get("archive_bytes") == metadata["archive_bytes"]
        )
        if not provenance_ok:
            return {
                "submitted": True,
                "resumed": True,
                "returncode": 1,
                "reason": "untrusted_preexisting_aristotle_archive",
            }
        return {
            "submitted": True,
            "resumed": True,
            "returncode": 0,
            "archive": str(archive),
            "reason": "result_archive_already_present",
        }
    if isinstance(previous_state, dict):
        if previous_state.get("automatic_resubmit_forbidden") is True:
            return {
                "submitted": True,
                "resumed": True,
                "returncode": 1,
                "reason": "ambiguous_aristotle_submission_without_id",
                "automatic_resubmit_forbidden": True,
            }
        project_id = previous_state.get("project_id")
        task_id = previous_state.get("task_id")
        if not (project_id and task_id):
            previous_log = iter_dir / "aristotle_submit.log"
            if previous_log.exists():
                project_id, task_id = parse_aristotle_ids(
                    previous_log.read_text(encoding="utf-8", errors="replace")
                )
                if project_id and task_id:
                    write_json(state_path, {
                        "project_id": project_id,
                        "task_id": task_id,
                        "recovered_at": utc_now(),
                    })
        if project_id and not task_id:
            task_id, discovery = discover_aristotle_task_id(project_id)
            if task_id:
                write_json(state_path, {
                    "project_id": project_id,
                    "task_id": task_id,
                    "task_discovered_at": utc_now(),
                })
            else:
                return {
                    "submitted": True,
                    "resumed": True,
                    "returncode": 1,
                    "project_id": project_id,
                    "task_id": None,
                    "followup": {
                        "returncode": 1,
                        "status": "UNKNOWN",
                        "reason": "timeout_waiting_for_aristotle_task_id",
                        "discovery": discovery,
                    },
                }
        if project_id and task_id:
            followup = wait_for_aristotle_and_download(
                iter_dir, project_id, task_id, archive,
                timeout_seconds=timeout_seconds,
            )
            return {
                "submitted": True,
                "resumed": True,
                "returncode": followup["returncode"],
                "project_id": project_id,
                "task_id": task_id,
                "followup": followup,
            }
    previous_log = iter_dir / "aristotle_submit.log"
    if previous_log.exists() and not previous_state:
        prior_output = previous_log.read_text(encoding="utf-8", errors="replace")
        prior_project, prior_task = parse_aristotle_ids(prior_output)
        if not prior_project:
            write_json(state_path, {
                "submission_status": "ambiguous_no_id",
                "automatic_resubmit_forbidden": True,
                "recovered_at": utc_now(),
            })
            return {
                "submitted": True,
                "resumed": True,
                "returncode": 1,
                "reason": "ambiguous_aristotle_submission_without_id",
                "automatic_resubmit_forbidden": True,
            }
    # Persist the intent *before* crossing the network boundary.  If this
    # process or the VM dies after the service accepts the remote submission but
    # before an id reaches stdout, a resumed runner must not submit again.
    # A human can reconcile the service state and replace/clear this guard.
    write_json(state_path, {
        "submission_status": "submitting_unknown_outcome",
        "automatic_resubmit_forbidden": True,
        "attempt_started_at": utc_now(),
    })
    # Submission is deliberately attempted exactly once.  If the connection
    # drops before the project id is printed, retrying could create a duplicate
    # project and ambiguous provenance; that case requires reconciliation.
    for attempt in range(1, 2):
        try:
            cp = run_group_capture(
                ["python3", str(script)],
                cwd=iter_dir,
                input_text=None,
                env=None,
                timeout=min(600, max(120, timeout_seconds)),
            )
        except Exception as exc:
            write_json(state_path, {
                "submission_status": "ambiguous_no_id",
                "automatic_resubmit_forbidden": True,
                "exception": f"{type(exc).__name__}: {exc}",
                "recorded_at": utc_now(),
            })
            return {
                "submitted": True,
                "returncode": 1,
                "reason": "ambiguous_aristotle_submission_without_id",
                "automatic_resubmit_forbidden": True,
            }
        attempts.append((attempt, cp))
        output = cp.stdout + cp.stderr
        project_id, task_id = parse_aristotle_ids(output)
        if project_id:
            break
    output = "\n\n".join(
        f"===== Aristotle submit attempt {attempt}/1 =====\n{cp.stdout}{cp.stderr}"
        for attempt, cp in attempts
    )
    write_text(iter_dir / "aristotle_submit.log", output)
    project_id, task_id = parse_aristotle_ids(output)
    if project_id:
        write_json(state_path, {
            "project_id": project_id,
            "task_id": task_id,
            "submitted_at": utc_now(),
        })
        if not task_id:
            task_id, discovery = discover_aristotle_task_id(project_id)
            if not task_id:
                return {
                    "submitted": True,
                    "returncode": 1,
                    "initial_returncode": cp.returncode,
                    "project_id": project_id,
                    "task_id": None,
                    "followup": {
                        "returncode": 1,
                        "status": "UNKNOWN",
                        "reason": "timeout_waiting_for_aristotle_task_id",
                        "discovery": discovery,
                    },
                }
            write_json(state_path, {
                "project_id": project_id,
                "task_id": task_id,
                "submitted_at": utc_now(),
                "task_discovered_at": utc_now(),
            })
        followup = wait_for_aristotle_and_download(iter_dir, project_id, task_id, archive, timeout_seconds=timeout_seconds)
        return {
            "submitted": True,
            "returncode": followup["returncode"],
            "initial_returncode": cp.returncode,
            "project_id": project_id,
            "task_id": task_id,
            "followup": followup,
        }
    write_json(state_path, {
        "submission_status": "ambiguous_no_id",
        "automatic_resubmit_forbidden": True,
        "initial_returncode": cp.returncode,
        "recorded_at": utc_now(),
    })
    return {
        "submitted": True,
        "returncode": 1,
        "initial_returncode": cp.returncode,
        "reason": "ambiguous_aristotle_submission_without_id",
        "automatic_resubmit_forbidden": True,
        "project_id": project_id,
        "task_id": task_id,
    }


def parse_aristotle_ids(output: str) -> tuple[str | None, str | None]:
    project_id = None
    task_id = None
    for line in output.splitlines():
        line = line.strip()
        if line.startswith("Project created:"):
            project_id = line.split(":", 1)[1].strip()
        elif line.startswith("Project:"):
            project_id = line.split(":", 1)[1].strip()
        elif line.startswith("Task:"):
            task_id = line.split(":", 1)[1].strip()
    return project_id, task_id


def discover_aristotle_task_id(
    project_id: str,
    *,
    timeout_seconds: int = 600,
    poll_seconds: int = 10,
) -> tuple[str | None, str]:
    """Discover the task created asynchronously for a project, without resubmission."""
    started = time.monotonic()
    logs: list[str] = []
    uuid_pattern = re.compile(
        r"\b[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-"
        r"[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\b"
    )
    while time.monotonic() - started < timeout_seconds:
        rc, output = command_output(
            [str(ARISTOTLE_BIN), "tasks", project_id, "--limit", "5"],
            ROOT,
            timeout=60,
        )
        logs.append(f"[{utc_now()}] rc={rc}\n{output}")
        if rc == 0:
            _, parsed_task = parse_aristotle_ids(output)
            if parsed_task:
                return parsed_task, "\n".join(logs)
            candidates = [value for value in uuid_pattern.findall(output) if value != project_id]
            if candidates:
                return candidates[0], "\n".join(logs)
            terminal_words = {
                "QUEUED", "IN_PROGRESS", "COMPLETE", "COMPLETED",
                "FAILED", "ERROR", "CANCELED", "CANCELLED", "OUT_OF_BUDGET",
            }
            for line in output.splitlines():
                tokens = line.strip().split()
                if not tokens or not any(token.upper() in terminal_words for token in tokens):
                    continue
                candidate = tokens[0].strip("|[],:;")
                if candidate and candidate != project_id and candidate.lower() not in {"task", "id"}:
                    return candidate, "\n".join(logs)
        time.sleep(poll_seconds)
    return None, "\n".join(logs)


def aristotle_task_status(project_id: str, task_id: str) -> tuple[str, str]:
    rc, out = command_output(
        [str(ARISTOTLE_BIN), "tasks", project_id, "--limit", "5"],
        ROOT,
        timeout=60,
    )
    if rc != 0:
        return "UNKNOWN", out
    for line in out.splitlines():
        if task_id in line:
            parts = line.split()
            if parts:
                return parts[-1], out
    return "UNKNOWN", out


def wait_for_aristotle_and_download(
    iter_dir: Path,
    project_id: str,
    task_id: str,
    archive: Path,
    *,
    timeout_seconds: int = 7200,
    poll_seconds: int = 300,
) -> dict[str, Any]:
    log_path = iter_dir / "aristotle_followup.log"
    started = time.monotonic()
    last_status = "UNKNOWN"
    while time.monotonic() - started < timeout_seconds:
        status, out = aristotle_task_status(project_id, task_id)
        last_status = status
        with log_path.open("a", encoding="utf-8") as handle:
            handle.write(f"\n[{utc_now()}] status={status}\n")
            handle.write(out)
            if not out.endswith("\n"):
                handle.write("\n")
        if status not in {"IN_PROGRESS", "QUEUED", "UNKNOWN"}:
            break
        time.sleep(poll_seconds)
    if last_status in {"IN_PROGRESS", "QUEUED", "UNKNOWN"}:
        return {"returncode": 1, "status": last_status, "reason": "timeout_waiting_for_aristotle"}
    if last_status in {"CANCELED", "CANCELLED", "FAILED", "ERROR"}:
        return {
            "returncode": 1,
            "status": last_status,
            "reason": "aristotle_terminal_failure",
        }

    temporary_archive = iter_dir / "aristotle_result.download.tmp"
    if os.path.lexists(temporary_archive):
        if temporary_archive.is_dir() and not temporary_archive.is_symlink():
            raise RuntimeError(f"refusing unexpected download directory: {temporary_archive}")
        temporary_archive.unlink()
        fsync_directory(iter_dir)
    cp = subprocess.run(
        [str(ARISTOTLE_BIN), "download", project_id, "--destination", str(temporary_archive)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=1200,
    )
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(f"\n[{utc_now()}] download returncode={cp.returncode}\n")
        handle.write(cp.stdout)
        if not cp.stdout.endswith("\n"):
            handle.write("\n")
    if cp.returncode != 0:
        if os.path.lexists(temporary_archive) and not temporary_archive.is_dir():
            temporary_archive.unlink()
            fsync_directory(iter_dir)
        return {
            "returncode": cp.returncode,
            "status": last_status,
            "reason": "aristotle_download_failed",
        }
    try:
        metadata = validate_aristotle_archive(temporary_archive, iter_dir)
    except Exception as exc:
        if os.path.lexists(temporary_archive) and not temporary_archive.is_dir():
            temporary_archive.unlink()
            fsync_directory(iter_dir)
        return {
            "returncode": 1,
            "status": last_status,
            "reason": "invalid_aristotle_download",
            "archive_error": f"{type(exc).__name__}: {exc}",
        }
    if os.path.lexists(archive):
        return {
            "returncode": 1,
            "status": last_status,
            "reason": "final_aristotle_archive_appeared_during_download",
        }
    os.replace(temporary_archive, archive)
    fsync_directory(iter_dir)
    write_json(iter_dir / "aristotle_state.json", {
        "project_id": project_id,
        "task_id": task_id,
        "archive_project_id": project_id,
        "archive_task_id": task_id,
        "archive_sha256": metadata["archive_sha256"],
        "archive_bytes": metadata["archive_bytes"],
        "archive_validated_at": utc_now(),
    })
    return {
        "returncode": 0,
        "status": last_status,
        "archive": str(archive),
        **metadata,
    }


def terminate_process_group(process: subprocess.Popen[str]) -> None:
    """Terminate the isolated agent group, including descendants after leader exit."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        pass
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.2)
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    if process.poll() is None:
        process.wait(timeout=10)


def run_group_capture(
    cmd: list[str],
    *,
    cwd: Path,
    input_text: str | None,
    env: dict[str, str] | None,
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    # Agent CLIs sometimes leave background `tail -f` helpers that inherit
    # stdout/stderr. Pipes then never reach EOF even after the agent leader
    # exits, so `communicate()` can hang forever. Regular temporary files avoid
    # that pipe-lifetime trap and also keep very large agent transcripts out of
    # the runner's resident memory while the command is active.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout_file, tempfile.TemporaryFile(
        mode="w+", encoding="utf-8"
    ) as stderr_file:
        process = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.PIPE if input_text is not None else subprocess.DEVNULL,
            stdout=stdout_file,
            stderr=stderr_file,
            text=True,
            start_new_session=True,
        )
        timed_out = False
        try:
            process.communicate(input=input_text, timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
        finally:
            terminate_process_group(process)

        stdout_file.seek(0)
        stderr_file.seek(0)
        stdout = stdout_file.read()
        stderr = stderr_file.read()
        if timed_out:
            raise TimeoutError(
                f"process group timed out after {timeout}s and was terminated: {' '.join(cmd)}\n"
                f"stdout:\n{stdout[-4000:]}\nstderr:\n{stderr[-4000:]}"
            )
        return subprocess.CompletedProcess(cmd, process.returncode, stdout, stderr)


def run_process_capture(
    *,
    name: str,
    cmd: list[str],
    cwd: Path,
    prompt: str | None,
    out_dir: Path,
    timeout: int,
) -> tuple[bool, str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    hp = import_pipeline_module()
    env = hp.model_env()
    prompt_path = out_dir / f"{name}.prompt.md"
    raw_path = out_dir / f"{name}.raw.json"
    started_at = utc_now()
    started = time.monotonic()
    try:
        completed = run_group_capture(
            cmd,
            cwd=str(cwd),
            input_text=prompt,
            env=env,
            timeout=timeout,
        )
        payload = {
            "name": name,
            "cmd": cmd,
            "cwd": str(cwd),
            "returncode": completed.returncode,
            "started_at": started_at,
            "finished_at": utc_now(),
            "duration_seconds": round(time.monotonic() - started, 3),
            "stdout": completed.stdout,
            "stderr": completed.stderr,
            "prompt_path": str(prompt_path),
        }
        write_json(raw_path, payload)
        if completed.returncode != 0:
            raise RuntimeError(f"{name} failed with exit code {completed.returncode}; see {raw_path}")
        text = str(payload.get("stdout", "")).strip()
        if not text:
            text = f"STATUS: EMPTY_OUTPUT\n\nCommand completed but produced empty stdout.\n"
        write_text(out_dir / f"{name}.md", text + "\n")
        return True, text
    except Exception as exc:
        text = (
            f"STATUS: FAILED\n\nagent_id: `{name}`\n\n"
            f"error: `{type(exc).__name__}: {exc}`\n\n"
            "Traceback:\n\n```text\n"
            f"{traceback.format_exc()}```\n"
        )
        write_text(out_dir / f"{name}.FAILED.md", text)
        return False, text


def command_output(argv: list[str], cwd: Path, timeout: int = 1800) -> tuple[int, str]:
    cp = run_group_capture(argv, cwd=cwd, input_text=None, env=None, timeout=timeout)
    return cp.returncode, cp.stdout + cp.stderr


def run_edit_agent(
    kind: str,
    agent_id: str,
    prompt: str,
    out_dir: Path,
    timeout: int,
    dry_run: bool,
    work_root: Path,
) -> tuple[bool, str]:
    agent_scratch = out_dir / "agent_scratch" / agent_id
    agent_scratch.mkdir(parents=True, exist_ok=True)
    checkpoint_path = agent_scratch / "checkpoint.md"
    checkpoint_msg = f"""

Checkpoint protocol:
- Immediately create or update `{checkpoint_path}` if your tool surface can
  write files.
- If you work for more than about 10 minutes, append useful partial progress to
  that checkpoint every ~10 minutes: candidate proof terms, exact theorem names,
  failed tactics, local lemmas, obstacles, or any useful partial Lean code.
- If you cannot write files, include a `Checkpoint summary` section in stdout.
"""
    prompt = prompt.rstrip() + checkpoint_msg
    prompt_path = agent_scratch / "prompt.md"
    write_text(prompt_path, prompt)
    write_text(out_dir / f"{agent_id}.prompt.md", prompt)
    if dry_run:
        text = f"STATUS: DRY_RUN\n\nPrompt written to `{prompt_path}`.\n"
        write_text(out_dir / f"{agent_id}.md", text)
        return True, text
    hp = import_pipeline_module()
    if kind == "gemini":
        launcher_prompt = (
            "Read the full task prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            "You have write access to the worktree. Edit files there if useful, "
            "then report what changed. Preserve partial progress using the "
            f"checkpoint file `{checkpoint_path}`."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--sandbox",
            "--mode",
            "accept-edits",
            "--model",
            GEMINI_MODEL,
            "--effort",
            GEMINI_EFFORT,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(agent_scratch),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt="", out_dir=out_dir, timeout=timeout)
    if kind == "codex":
        cmd = [
            hp.CODEX_BIN,
            "exec",
            "--ephemeral",
            "--skip-git-repo-check",
            "--sandbox",
            "workspace-write",
            "-C",
            str(work_root),
            "--color",
            "never",
            "-m",
            CODEX_MODEL,
            "-c",
            f'model_reasoning_effort="{CODEX_EFFORT}"',
            "-",
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt=prompt, out_dir=out_dir, timeout=timeout)
    if kind == "claude":
        launcher_prompt = (
            "Read the full task prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            "You have write access to the worktree. Edit files there if useful, "
            "then report what changed. Preserve partial progress using the "
            f"checkpoint file `{checkpoint_path}`."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--sandbox",
            "--mode",
            "accept-edits",
            "--model",
            CLAUDE_MODEL,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(agent_scratch),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(name=agent_id, cmd=cmd, cwd=work_root, prompt="", out_dir=out_dir, timeout=timeout)
    raise ValueError(f"unsupported edit agent kind: {kind}")


def run_strategy_agent(
    kind: str,
    agent_id: str,
    prompt: str,
    out_dir: Path,
    timeout: int,
    dry_run: bool,
    work_root: Path,
) -> tuple[bool, str]:
    agent_scratch = out_dir / "agent_scratch" / agent_id
    agent_scratch.mkdir(parents=True, exist_ok=True)
    prompt_path = agent_scratch / "prompt.md"
    write_text(prompt_path, prompt)
    write_text(out_dir / f"{agent_id}.prompt.md", prompt)
    if dry_run:
        text = f"STATUS: DRY_RUN\n\nPrompt written to `{prompt_path}`.\n"
        write_text(out_dir / f"{agent_id}.md", text)
        return True, text
    hp = import_pipeline_module()
    if kind == "gemini":
        launcher_prompt = (
            "Read the full strategy prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            f"The current repository is the worktree `{work_root}`, not the parent/root checkout. "
            "Do not edit Lean files during this strategy iteration."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--mode",
            "plan",
            "--sandbox",
            "--model",
            GEMINI_MODEL,
            "--effort",
            GEMINI_EFFORT,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(agent_scratch),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt="",
            out_dir=out_dir,
            timeout=timeout,
        )
    if kind == "codex":
        cmd = [
            hp.CODEX_BIN,
            "exec",
            "--ephemeral",
            "--skip-git-repo-check",
            "--sandbox",
            "read-only",
            "-C",
            str(work_root),
            "--color",
            "never",
            "-m",
            CODEX_MODEL,
            "-c",
            f'model_reasoning_effort="{CODEX_EFFORT}"',
            "-",
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt=prompt,
            out_dir=out_dir,
            timeout=timeout,
        )
    if kind == "claude":
        launcher_prompt = (
            "Read the full strategy prompt from this file and follow it exactly:\n"
            f"{prompt_path}\n\n"
            f"The current repository is the worktree `{work_root}`, not the parent/root checkout. "
            "Do not edit Lean files during this strategy iteration."
        )
        cmd = [
            hp.AGY_BIN,
            "--dangerously-skip-permissions",
            "--mode",
            "plan",
            "--sandbox",
            "--model",
            CLAUDE_MODEL,
            "--print-timeout",
            f"{max(60, timeout - 30)}s",
            "--add-dir",
            str(work_root),
            "--add-dir",
            str(agent_scratch),
            "--print",
            launcher_prompt,
        ]
        return run_process_capture(
            name=agent_id,
            cmd=cmd,
            cwd=work_root,
            prompt="",
            out_dir=out_dir,
            timeout=timeout,
        )
    raise ValueError(f"unsupported strategy agent kind: {kind}")


def prepare_worktree(section_dir: Path) -> Path:
    work_root = section_dir / "_worktree"
    if work_root.exists():
        return work_root

    def ignore(_: str, names: list[str]) -> set[str]:
        ignored = {
            ".git",
            ".lake",
            "proof_loop_runs",
            "proof_loop_readiness",
            "interface_part_reviews",
            "reviews",
        }
        return {name for name in names if name in ignored or name.endswith(".olean") or name.endswith(".ilean")}

    shutil.copytree(ROOT, work_root, ignore=ignore)
    command_output(["git", "init", "-q"], work_root, timeout=60)
    command_output(["git", "add", "."], work_root, timeout=120)
    command_output(
        ["git", "-c", "user.name=proof-loop", "-c", "user.email=proof-loop@example.invalid", "commit", "-q", "-m", "baseline"],
        work_root,
        timeout=120,
    )
    lake = work_root / ".lake"
    lake.mkdir(exist_ok=True)
    # Packages/config are shared read-mostly to avoid duplicating the 6.9 GiB
    # pinned cache on this VM.  Agents run inside their own filesystem sandbox;
    # after every stage check_dependencies.py verifies both Git revisions and a
    # frozen digest of *all* non-.git dependency bytes, including ignored build
    # artifacts.  Any write therefore blocks before merge.
    for name in ["packages", "config"]:
        src = ROOT / ".lake" / name
        dst = lake / name
        if src.exists() and not dst.exists():
            dst.symlink_to(src, target_is_directory=src.is_dir())
    # Seed the project build artifacts from ROOT so the first worktree
    # build is incremental (only files the agents touch get rebuilt).
    build_src = ROOT / ".lake" / "build"
    build_dst = lake / "build"
    if build_src.exists() and not build_dst.exists():
        shutil.copytree(build_src, build_dst)
    return work_root


def allowed_prefixes(section: dict[str, Any]) -> list[str]:
    return [str(p) for p in section.get("allowed_prefixes", [])]


def is_allowed_candidate(rel: str, section: dict[str, Any]) -> bool:
    forbidden = [str(p) for p in section.get("forbidden_prefixes", [])]
    if any(rel == prefix.rstrip("/") or rel.startswith(prefix) for prefix in forbidden):
        return False
    return any(rel == prefix.rstrip("/") or rel.startswith(prefix) for prefix in allowed_prefixes(section))


def iter_candidate_files(root: Path, section: dict[str, Any]) -> list[Path]:
    files: list[Path] = []
    for prefix in allowed_prefixes(section):
        path = root / prefix
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.lean"))
    return sorted(set(files))


def iter_mergeable_files(root: Path, section: dict[str, Any]) -> list[Path]:
    files = list(iter_candidate_files(root, section))
    for prefix in allowed_prefixes(section):
        path = root / prefix
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.md"))
    return sorted(set(files))


def changed_candidate_files(work_root: Path, section: dict[str, Any]) -> list[tuple[str, Path]]:
    changed: list[tuple[str, Path]] = []
    for path in iter_mergeable_files(work_root, section):
        rel = path.relative_to(work_root).as_posix()
        if not is_allowed_candidate(rel, section):
            continue
        safe_path = safe_project_target(work_root, rel)
        if safe_path != path:
            raise RuntimeError(f"non-canonical candidate path: {path}")
        root_path = ROOT / rel
        if not root_path.exists() or not filecmp.cmp(path, root_path, shallow=False):
            changed.append((rel, path))
    return changed


def safe_extract_project_tar(archive: Path, dest: Path) -> Path | None:
    """Extract an Aristotle result without trusting tar metadata.

    Only regular files and directories are accepted.  Links, devices, FIFOs,
    traversal, duplicate paths, and unbounded archives are rejected before any
    result is considered for integration.
    """
    max_members = 20_000
    max_file_bytes = 100 * 1024 * 1024
    max_total_bytes = 1024 * 1024 * 1024
    if not archive.exists():
        return None
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    dest_resolved = dest.resolve()
    with tarfile.open(archive, "r:gz") as tf:
        members = tf.getmembers()
        if len(members) > max_members:
            raise RuntimeError(f"tar has too many members: {len(members)}")
        selected: list[tuple[tarfile.TarInfo, Path]] = []
        seen: set[str] = set()
        total = 0
        for member in members:
            if "\\" in member.name:
                raise RuntimeError(f"unsafe backslash in tar member: {member.name}")
            pure = PurePosixPath(member.name)
            parts = tuple(part for part in pure.parts if part not in {"", "."})
            if pure.is_absolute() or ".." in parts:
                raise RuntimeError(f"unsafe tar member path: {member.name}")
            if not parts:
                continue
            if ".lake" in parts:
                continue
            rel = PurePosixPath(*parts).as_posix()
            if rel in seen:
                raise RuntimeError(f"duplicate tar member: {member.name}")
            seen.add(rel)
            if not (member.isdir() or member.isfile()):
                raise RuntimeError(f"unsupported tar member type: {member.name}")
            if member.isfile():
                if member.size < 0 or member.size > max_file_bytes:
                    raise RuntimeError(f"tar member too large: {member.name}")
                total += member.size
                if total > max_total_bytes:
                    raise RuntimeError("tar uncompressed size limit exceeded")
            target = (dest / Path(*parts)).resolve()
            try:
                target.relative_to(dest_resolved)
            except ValueError as exc:
                raise RuntimeError(f"unsafe tar member path: {member.name}") from exc
            selected.append((member, target))

        for member, target in selected:
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                target.chmod(0o755)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = tf.extractfile(member)
            if source is None:
                raise RuntimeError(f"cannot read regular tar member: {member.name}")
            with source, target.open("wb") as output:
                shutil.copyfileobj(source, output, length=1024 * 1024)
            if target.stat().st_size != member.size:
                raise RuntimeError(f"truncated tar member: {member.name}")
            target.chmod(0o644)
    candidates = sorted(
        list(dest.rglob("lakefile.lean")) + list(dest.rglob("lakefile.toml")),
        key=lambda p: len(p.parts))
    return candidates[0].parent if candidates else None


def integrate_aristotle_result(iter_dir: Path, work_root: Path, section: dict[str, Any]) -> dict[str, Any]:
    archive = iter_dir / "aristotle_result.tar.gz"
    if not archive.exists():
        return {"integrated": False, "reason": "missing_result_archive"}
    dest = iter_dir / "aristotle_unpacked"
    project = safe_extract_project_tar(archive, dest)
    if project is None:
        return {"integrated": False, "reason": "no_lakefile_in_archive"}
    submitted_name = project.name.removesuffix("_aristotle")
    submitted_project = iter_dir / submitted_name
    if not submitted_project.is_dir():
        return {
            "integrated": False,
            "reason": "missing_submitted_project_for_three_way_integration",
            "result_project": str(project),
            "expected_submitted_project": str(submitted_project),
        }
    copied: list[str] = []
    for src in iter_mergeable_files(project, section):
        rel = src.relative_to(project).as_posix()
        if not is_allowed_candidate(rel, section):
            continue
        submitted = safe_project_target(submitted_project, rel)
        if submitted.exists() and filecmp.cmp(src, submitted, shallow=False):
            continue
        dst = safe_project_target(work_root, rel)
        atomic_copy(src, dst)
        copied.append(rel)
    return {
        "integrated": True,
        "project": str(project),
        "submitted_project": str(submitted_project),
        "copied": copied,
    }


def extract_aristotle_strategy_note(iter_dir: Path) -> dict[str, Any]:
    archive = iter_dir / "aristotle_result.tar.gz"
    if not archive.exists():
        return {"extracted": False, "reason": "missing_result_archive"}
    project = safe_extract_project_tar(archive, iter_dir / "aristotle_unpacked")
    if project is None:
        return {"extracted": False, "reason": "no_lakefile_in_archive"}
    candidates = sorted(
        path
        for path in project.rglob("*.md")
        if "strategy" in path.name.lower() and path.name != "ARISTOTLE_SUMMARY.md"
    )
    if not candidates:
        summary = project / "ARISTOTLE_SUMMARY.md"
        candidates = [summary] if summary.exists() else []
    if not candidates:
        return {"extracted": False, "reason": "missing_strategy_note"}
    source = candidates[0]
    destination = iter_dir / "07_aristotle.md"
    shutil.copy2(source, destination)
    return {
        "extracted": True,
        "source": str(source),
        "destination": str(destination),
    }


def restore_backup(backup: dict[str, Path | None]) -> None:
    for rel, saved in backup.items():
        target = safe_project_target(ROOT, rel)
        if saved is None:
            if target.exists():
                target.unlink()
            continue
        atomic_copy(saved, target)


def merge_gate(section: dict[str, Any], work_root: Path, iter_dir: Path, args: argparse.Namespace) -> dict[str, Any]:
    gate_dir = iter_dir / "merge_gate"
    gate_dir.mkdir(parents=True, exist_ok=True)
    lock_path = ROOT / "proof_loop" / "MERGE_GATE.lock"
    before_count = count_sorries_at(ROOT)
    changed = changed_candidate_files(work_root, section)
    if not changed:
        result = {"status": "NO_CHANGES", "before_sorries": before_count, "changed": []}
        write_json(gate_dir / "result.json", result)
        return result

    with open_nofollow_lock(lock_path) as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        before_count = count_sorries_at(ROOT)
        backup_dir = gate_dir / "backup"
        if backup_dir.exists():
            shutil.rmtree(backup_dir)
        backup_dir.mkdir()
        backup: dict[str, Path | None] = {}
        copied: list[str] = []
        journal_path = ROOT / "proof_loop/MERGE_JOURNAL.json"
        try:
            # Back up every target before mutating any target.  The atomic
            # journal lets the next preflight recover after SIGKILL/power loss.
            for rel, src in changed:
                target = safe_project_target(ROOT, rel)
                if target.exists():
                    saved = backup_dir / rel
                    saved.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(target, saved)
                    backup[rel] = saved
                else:
                    backup[rel] = None
            write_json(journal_path, {
                "created_at": utc_now(),
                "entries": [
                    {
                        "rel": rel,
                        "existed": saved is not None,
                        "backup": str(saved) if saved is not None else None,
                        "backup_sha256": (
                            hashlib.sha256(saved.read_bytes()).hexdigest()
                            if saved is not None else None
                        ),
                    }
                    for rel, saved in backup.items()
                ],
            })
            for rel, src in changed:
                atomic_copy(src, safe_project_target(ROOT, rel))
                copied.append(rel)

            after_count = count_sorries_at(ROOT)
            allowed_after = before_count + args.max_sorry_increase_per_merge
            if after_count > allowed_after:
                restore_backup(backup)
                journal_path.unlink(missing_ok=True)
                restore_unexpected_canonical_changes()
                result = {
                    "status": "REJECTED",
                    "reason": "too_many_new_sorries",
                    "before_sorries": before_count,
                    "after_sorries": after_count,
                    "max_sorry_increase_per_merge": args.max_sorry_increase_per_merge,
                    "changed": copied,
                }
                write_json(gate_dir / "result.json", result)
                return result

            completion_rel = section.get("completion_file")
            audit_script = (
                "scripts/audit_release.sh"
                if completion_rel and (ROOT / completion_rel).exists()
                else "scripts/audit.sh"
            )
            audit_rc, audit_out = command_output(
                ["bash", audit_script], ROOT, timeout=args.audit_timeout_seconds
            )
            write_text(gate_dir / "audit.log", audit_out)
            if audit_rc != 0:
                restore_backup(backup)
                journal_path.unlink(missing_ok=True)
                restore_unexpected_canonical_changes()
                result = {
                    "status": "REJECTED",
                    "reason": "audit_failed",
                    "audit_rc": audit_rc,
                    "before_sorries": before_count,
                    "after_sorries": after_count,
                    "changed": copied,
                }
                write_json(gate_dir / "result.json", result)
                return result

            result = {
                "status": "ACCEPTED",
                "before_sorries": before_count,
                "after_sorries": after_count,
                "changed": copied,
            }
            journal_path.unlink(missing_ok=True)
            capture_canonical_tree_snapshot()
            write_json(gate_dir / "result.json", result)
            return result
        except Exception as exc:
            restore_backup(backup)
            journal_path.unlink(missing_ok=True)
            restore_unexpected_canonical_changes()
            result = {
                "status": "REJECTED",
                "reason": f"exception: {type(exc).__name__}: {exc}",
                "traceback": traceback.format_exc(),
                "changed": copied,
            }
            write_json(gate_dir / "result.json", result)
            return result


def sync_worktree_checkpoint(
    section: dict[str, Any], work_root: Path, iteration: int
) -> dict[str, Any]:
    """Make worktree HEAD match the accepted root after every merge decision."""
    root_files = {
        path.relative_to(ROOT).as_posix(): path
        for path in iter_mergeable_files(ROOT, section)
        if is_allowed_candidate(path.relative_to(ROOT).as_posix(), section)
    }
    work_files = {
        path.relative_to(work_root).as_posix(): path
        for path in iter_mergeable_files(work_root, section)
        if is_allowed_candidate(path.relative_to(work_root).as_posix(), section)
    }
    rels = sorted(set(root_files) | set(work_files))
    for rel in rels:
        source = root_files.get(rel)
        target = safe_project_target(work_root, rel)
        if source is None:
            target.unlink(missing_ok=True)
            continue
        atomic_copy(source, target)

    if not rels:
        return {"status": "NO_FILES"}
    stage_rels: list[str] = []
    for rel in rels:
        if (work_root / rel).exists():
            stage_rels.append(rel)
            continue
        tracked_rc, _ = command_output(
            ["git", "ls-files", "--error-unmatch", "--", rel],
            work_root,
            timeout=60,
        )
        if tracked_rc == 0:
            stage_rels.append(rel)
    if not stage_rels:
        return {"status": "UNCHANGED"}
    add_rc, add_out = command_output(
        ["git", "add", "-A", "--", *stage_rels], work_root, timeout=300
    )
    if add_rc != 0:
        raise RuntimeError(f"failed to stage worktree checkpoint:\n{add_out}")
    diff_rc, diff_out = command_output(
        ["git", "diff", "--cached", "--quiet"], work_root, timeout=120
    )
    if diff_rc == 0:
        return {"status": "UNCHANGED"}
    if diff_rc != 1:
        raise RuntimeError(f"failed to inspect worktree checkpoint:\n{diff_out}")
    commit_rc, commit_out = command_output(
        [
            "git",
            "-c",
            "user.name=proof-loop",
            "-c",
            "user.email=proof-loop@example.invalid",
            "commit",
            "-m",
            f"accepted root after iteration {iteration}",
        ],
        work_root,
        timeout=300,
    )
    if commit_rc != 0:
        raise RuntimeError(f"failed to commit worktree checkpoint:\n{commit_out}")
    head_rc, head_out = command_output(["git", "rev-parse", "HEAD"], work_root, timeout=60)
    if head_rc != 0:
        raise RuntimeError(f"failed to read worktree checkpoint HEAD:\n{head_out}")
    return {"status": "COMMITTED", "head": head_out.strip(), "files": len(rels)}


def run_iteration(
    section: dict[str, Any],
    section_dir: Path,
    iteration: int,
    args: argparse.Namespace,
    context: str,
    work_root: Path,
) -> dict[str, Any]:
    is_strategy = (
        args.strategy_every > 0
        and iteration >= args.strategy_first
        and (iteration - args.strategy_first) % args.strategy_every == 0
    )
    mode = "strategy" if is_strategy else "proof"
    iter_dir = section_dir / f"iter_{iteration:03d}_{mode}"
    iter_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = iter_dir / "manifest.json"
    existing_manifest = load_json(manifest_path, {})
    same_iteration = (
        existing_manifest.get("section") == section["id"]
        and existing_manifest.get("iteration") == iteration
        and existing_manifest.get("mode") == mode
        and isinstance(existing_manifest.get("stages"), list)
    )
    if same_iteration and existing_manifest.get("status") == "complete":
        return existing_manifest
    if (
        same_iteration
        and existing_manifest.get("status") != "complete"
    ):
        manifest = existing_manifest
        manifest["resumed_at"] = utc_now()
    else:
        manifest: dict[str, Any] = {
            "section": section["id"],
            "iteration": iteration,
            "mode": mode,
            "started_at": utc_now(),
            "stages": [],
        }
    write_json(iter_dir / "manifest.json", manifest)
    completed_stages = {
        str(stage.get("stage"))
        for stage in manifest.get("stages", [])
        if isinstance(stage, dict)
        and (stage.get("completed") is True or stage.get("verified") is True)
    }

    stages = [
        ("gemini", "01_gemini"),
        ("claude", "02_opus"),
    ]
    for kind, stage in stages:
        if stage in completed_stages and (iter_dir / f"{stage}.md").exists():
            continue
        if status := pause_status(args, section):
            mark_paused(manifest, status)
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        previous = previous_outputs(iter_dir)
        control_before = iteration_control_snapshot(iter_dir)
        if mode == "strategy":
            agent_root = prepare_strategy_snapshot(work_root, iter_dir, stage)
            strategy_context = collect_context(section, agent_root)
            prompt = strategy_prompt(
                stage, section, iteration, strategy_context, previous,
                args.strategy_every - 1, agent_root,
            )
            if str(work_root) in prompt:
                raise RuntimeError(
                    "strategy prompt leaked the live worktree path into a read-only round"
                )
            before_digest = project_tree_digest(agent_root)
            ok, text = run_strategy_agent(
                kind,
                stage,
                prompt,
                iter_dir,
                args.timeout_seconds,
                args.dry_run,
                agent_root,
            )
            strategy_edited = project_tree_digest(agent_root) != before_digest
            if strategy_edited:
                text += (
                    "\n\nWARNING: STRATEGY_EDIT_DISCARDED\n"
                    "A strategy-only agent modified its disposable snapshot; "
                    "the snapshot is disposable, so the pipeline continues.\n"
                )
        else:
            prompt = ordinary_prompt(stage, section, iteration, context, previous, work_root)
            ok, text = run_edit_agent(kind, stage, prompt, iter_dir, args.timeout_seconds, args.dry_run, work_root)
        control_after = iteration_control_snapshot(iter_dir)
        if control_after != control_before:
            manifest.setdefault("warnings", []).append({
                "kind": "agent_control_file_change",
                "stage": stage,
                "control_before": control_before,
                "control_after": control_after,
            })
            write_json(iter_dir / "manifest.json", manifest)
        manifest["stages"].append({"stage": stage, "kind": kind, "ok": ok, "chars": len(text)})
        write_json(iter_dir / "manifest.json", manifest)
        if not ok:
            manifest.setdefault("warnings", []).append({
                "kind": "agent_stage_failed_continuing_for_repair",
                "stage": stage,
            })
            write_json(iter_dir / "manifest.json", manifest)
        checked_root = agent_root if mode == "strategy" else work_root
        canonical_changes = restore_unexpected_canonical_changes()
        if canonical_changes:
            manifest.setdefault("warnings", []).append({
                "kind": "direct_canonical_change_restored",
                "stage": stage,
                "paths": canonical_changes,
            })
            write_json(iter_dir / "manifest.json", manifest)
        canonical_mismatches = protected_mismatches(ROOT)
        if canonical_mismatches:
            restore_protected(ROOT, canonical_mismatches)
            manifest.setdefault("warnings", []).append({
                "kind": "canonical_protected_files_restored",
                "stage": stage,
                "paths": canonical_mismatches,
            })
            write_json(iter_dir / "manifest.json", manifest)
        dependency_rc, dependency_out = command_output(
            ["python3", str(ROOT / "scripts/check_dependencies.py"), "--root", str(ROOT)],
            ROOT,
            timeout=300,
        )
        write_text(iter_dir / f"{stage}.dependencies.md", f"```text\n{dependency_out}\n```\n")
        if dependency_rc != 0:
            manifest.setdefault("warnings", []).append({
                "kind": "canonical_dependency_check_failed",
                "stage": stage,
                "returncode": dependency_rc,
            })
            write_json(iter_dir / "manifest.json", manifest)
        mismatches = protected_mismatches(checked_root)
        if mismatches:
            restore_protected(checked_root, mismatches)
            manifest.setdefault("warnings", []).append({
                "kind": "protected_files_restored",
                "stage": stage,
                "paths": mismatches,
            })
            write_json(iter_dir / "manifest.json", manifest)
        trust_rc, trust_out = command_output(
            ["python3", str(ROOT / "scripts/check_trust.py"), "--root", str(checked_root)],
            ROOT,
            timeout=180,
        )
        write_text(iter_dir / f"{stage}.trust.md", f"```text\n{trust_out}\n```\n")
        if trust_rc != 0:
            manifest.setdefault("warnings", []).append({
                "kind": "stage_trust_failed_continuing_for_repair",
                "stage": stage,
                "returncode": trust_rc,
            })
            write_json(iter_dir / "manifest.json", manifest)
        audit_rc = 0
        if mode != "strategy" and not args.dry_run:
            audit_rc, audit_out = command_output(
                ["bash", "scripts/audit.sh"], work_root,
                timeout=args.audit_timeout_seconds,
            )
            write_text(iter_dir / f"{stage}.audit.md", f"```text\n{audit_out}\n```\n")
            manifest["stages"][-1]["audit_rc"] = audit_rc
            write_json(iter_dir / "manifest.json", manifest)
            if audit_rc != 0:
                manifest.setdefault("warnings", []).append({
                    "kind": "stage_audit_failed_continuing_for_repair",
                    "stage": stage,
                    "returncode": audit_rc,
                })
                write_json(iter_dir / "manifest.json", manifest)
        manifest["stages"][-1]["trust_rc"] = trust_rc
        manifest["stages"][-1]["completed"] = True
        manifest["stages"][-1]["verified"] = bool(
            ok and trust_rc == 0 and audit_rc == 0
        )
        write_json(iter_dir / "manifest.json", manifest)
        if status := pause_status(args, section):
            mark_paused(manifest, status, paused_after_stage=stage)
            write_json(iter_dir / "manifest.json", manifest)
            return manifest

    if status := pause_status(args, section):
        mark_paused(manifest, status, paused_before_aristotle=True)
        write_json(iter_dir / "manifest.json", manifest)
        return manifest

    open_leaves = count_section_sorries_at(work_root, section)
    manifest["open_leaves_after_stages"] = open_leaves
    if mode != "strategy" and not args.dry_run:
        manifest["local_merge_gate"] = {
            "status": "DEFERRED_UNTIL_AFTER_ARISTOTLE",
            "open_leaves": open_leaves,
            "reason": "One authoritative merge/audit is run after the third stage.",
        }

    aristotle_prompt = write_aristotle_packet(section, iteration, iter_dir, mode, work_root)
    manifest["aristotle_prompt"] = str(aristotle_prompt)
    should_submit_aristotle = (
        mode == "strategy"
        or open_leaves > 0
        or is_polishing(section)
        or bool(section.get("always_submit_aristotle"))
    )
    if args.submit_aristotle and not args.dry_run and should_submit_aristotle:
        manifest["aristotle"] = submit_aristotle(iter_dir, args.aristotle_timeout_seconds)
        if manifest["aristotle"].get("reason") == "ambiguous_aristotle_submission_without_id":
            manifest["status"] = "blocked_aristotle_ambiguous_submission"
            manifest["blocked_reason"] = (
                "Submission may have been accepted without returning an id; "
                "automatic resubmission is forbidden pending human reconciliation."
            )
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        followup = manifest["aristotle"].get("followup", {}) if isinstance(manifest.get("aristotle"), dict) else {}
        if str(followup.get("reason", "")).startswith("timeout_waiting_for_aristotle"):
            manifest["status"] = "waiting_aristotle"
            manifest["waiting_since"] = utc_now()
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        terminal_status = str(followup.get("status", "")).upper()
        if terminal_status in {"CANCELED", "CANCELLED", "FAILED", "ERROR"}:
            manifest["status"] = "blocked_aristotle_terminal_status"
            manifest["blocked_reason"] = (
                f"Refusing to integrate Aristotle result with terminal status {terminal_status}."
            )
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        if int(manifest["aristotle"].get("returncode", 1)) != 0:
            manifest["status"] = "blocked_aristotle_result_failure"
            manifest["blocked_reason"] = str(
                followup.get("reason")
                or manifest["aristotle"].get("reason")
                or "Aristotle stage returned a nonzero status."
            )
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        if not (iter_dir / "aristotle_result.tar.gz").exists():
            manifest["status"] = "blocked_missing_aristotle_result"
            manifest["blocked_reason"] = (
                "The required third stage did not produce a downloadable Aristotle archive."
            )
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        if mode == "strategy":
            manifest["aristotle_strategy_note"] = extract_aristotle_strategy_note(iter_dir)
            if not manifest["aristotle_strategy_note"].get("extracted"):
                manifest["status"] = "blocked_missing_aristotle_strategy_note"
                manifest["blocked_reason"] = "Aristotle archive contains no strategic result note."
                write_json(iter_dir / "manifest.json", manifest)
                return manifest
        # Aristotle can return a useful archive even when its task status is
        # OUT_OF_BUDGET. Explicit failure and cancellation statuses are blocked
        # above; the merge gate remains authoritative for useful partial work.
        if mode != "strategy" and (iter_dir / "aristotle_result.tar.gz").exists():
            manifest["aristotle_integration"] = integrate_aristotle_result(iter_dir, work_root, section)
    else:
        manifest["aristotle"] = {
            "submitted": False,
            "reason": "no_actionable_packet" if not should_submit_aristotle else "default_prepare_only",
        }
    if mode != "strategy" and not args.dry_run:
        integration = manifest.get("aristotle_integration", {}) if isinstance(manifest.get("aristotle_integration"), dict) else {}
        if args.submit_aristotle and should_submit_aristotle and not integration.get("integrated"):
            manifest["status"] = "blocked_missing_aristotle_result"
            manifest["blocked_reason"] = "Aristotle result was not downloaded/integrated; refusing LLM-only merge."
            write_json(iter_dir / "manifest.json", manifest)
            return manifest
        manifest["merge_gate"] = merge_gate(section, work_root, iter_dir, args)
        merge_status = manifest["merge_gate"].get("status")
        if merge_status in {"ACCEPTED", "NO_CHANGES"}:
            manifest["worktree_checkpoint"] = sync_worktree_checkpoint(
                section, work_root, iteration
            )
        else:
            manifest["worktree_checkpoint"] = {
                "status": "PRESERVED_UNMERGED",
                "reason": (
                    "The merge was rejected; keep the agent/Aristotle worktree "
                    "intact for repair in the next iteration."
                ),
            }
    manifest["status"] = "complete"
    manifest["finished_at"] = utc_now()
    write_json(iter_dir / "manifest.json", manifest)
    return manifest


def run_section(section: dict[str, Any], run_dir: Path, args: argparse.Namespace) -> dict[str, Any]:
    section_dir = run_dir / section["id"]
    section_dir.mkdir(parents=True, exist_ok=True)
    work_root = prepare_worktree(section_dir)
    context = collect_context(section, work_root)
    write_text(section_dir / "section_context.md", context)
    results = []
    iteration = args.start_iteration
    completed = 0
    while args.until_zero_sorries or completed < args.iterations:
        completion_rel = section.get("completion_file")
        if completion_rel and (ROOT / completion_rel).exists():
            release_rc, release_out = command_output(
                ["bash", "scripts/audit_release.sh"], ROOT,
                timeout=args.audit_timeout_seconds,
            )
            write_text(section_dir / "completion_release_audit.log", release_out)
            if release_rc != 0:
                raise RuntimeError(
                    f"completion marker exists but release audit failed (rc={release_rc})"
                )
            break
        if not args.until_zero_sorries and completed >= args.iterations:
            break
        if args.until_zero_sorries and count_sorries_at(ROOT) == 0:
            break
        if args.until_zero_sorries and count_section_sorries_at(ROOT, section) == 0:
            break
        if pause_status(args, section):
            break
        result = run_iteration(section, section_dir, iteration, args, context, work_root)
        results.append(result)
        if result.get("status") == "waiting_aristotle":
            time.sleep(300)
            continue
        if result.get("status") in BLOCKING_STATUSES:
            break
        iteration += 1
        completed += 1
    summary = {
        "section": section["id"],
        "title": section["title"],
        "iterations_requested": args.iterations,
        "iterations_completed": len(results),
        "results": results,
    }
    write_json(section_dir / "section_summary.json", summary)
    return summary


def selected_sections(args: argparse.Namespace, sections: list[dict[str, Any]]) -> list[dict[str, Any]]:
    requested = args.section or ["all"]
    if "all" in requested:
        return sections
    by_id = {section["id"]: section for section in sections}
    missing = [item for item in requested if item not in by_id]
    if missing:
        raise SystemExit(f"unknown section(s): {', '.join(missing)}")
    return [by_id[item] for item in requested]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--section", action="append", help="Section id, or all. May be repeated.")
    parser.add_argument("--list-sections", action="store_true")
    parser.add_argument("--iterations", type=int, default=1)
    parser.add_argument("--start-iteration", type=int, default=1)
    parser.add_argument("--strategy-first", type=int, default=1)
    parser.add_argument("--strategy-every", type=int, default=5)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--aristotle-timeout-seconds", type=int, default=86400)
    parser.add_argument("--run-dir", type=Path, default=None)
    parser.add_argument("--runs-root", type=Path, default=DEFAULT_RUNS_DIR)
    parser.add_argument("--stop-file", type=Path, default=DEFAULT_STOP_FILE)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--submit-aristotle", action="store_true")
    parser.add_argument("--until-zero-sorries", action="store_true")
    parser.add_argument("--max-sorry-increase-per-merge", type=int, default=10**9)
    parser.add_argument("--audit-timeout-seconds", type=int, default=1800)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    sections = load_sections()
    if args.list_sections:
        for section in sections:
            print(f"{section['id']}: {section['title']}")
        return 0

    acquire_runner_lock()
    run_dir = (args.run_dir or (args.runs_root / f"{utc_stamp()}-proof-section-loop")).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    preflight = production_preflight(args)
    capture_protected_snapshot()
    capture_canonical_tree_snapshot()
    write_json(run_dir / "preflight.json", preflight)
    write_json(
        run_dir / "manifest.json",
        {
            "started_at": utc_now(),
            "root": str(ROOT),
            "run_dir": str(run_dir),
            "dry_run": args.dry_run,
            "submit_aristotle": args.submit_aristotle,
            "aristotle_timeout_seconds": args.aristotle_timeout_seconds,
            "strategy_every": args.strategy_every,
            "strategy_first": args.strategy_first,
            "iterations": args.iterations,
            "sections": args.section or ["all"],
            "models": {
                "gemini": GEMINI_MODEL,
                "gemini_effort": GEMINI_EFFORT,
                "opus": CLAUDE_MODEL,
                "opus_effort": CLAUDE_EFFORT,
                "opus_runner": "agy CLI (model claude-opus-4-6-thinking)",
                "aristotle": str(ARISTOTLE_BIN),
            },
        },
    )
    chosen = selected_sections(args, sections)

    summaries: list[dict[str, Any]] = []
    errors: list[dict[str, str]] = []
    if args.jobs <= 1 or len(chosen) <= 1:
        for section in chosen:
            try:
                summaries.append(run_section(section, run_dir, args))
            except Exception as exc:
                errors.append({"section": section["id"], "error": f"{type(exc).__name__}: {exc}", "traceback": traceback.format_exc()})
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {pool.submit(run_section, section, run_dir, args): section for section in chosen}
            for future in as_completed(futures):
                section = futures[future]
                try:
                    summaries.append(future.result())
                except Exception as exc:
                    errors.append({"section": section["id"], "error": f"{type(exc).__name__}: {exc}", "traceback": traceback.format_exc()})

    write_json(run_dir / "SUMMARY.json", {"summaries": summaries, "errors": errors})
    lines = ["# Proof Section Loop Summary", "", f"- run_dir: `{run_dir}`", f"- dry_run: `{args.dry_run}`", ""]
    for summary in sorted(summaries, key=lambda x: x["section"]):
        lines.append(f"- {summary['section']}: {summary['iterations_completed']} iteration(s)")
    if errors:
        lines.append("")
        lines.append("## Errors")
        for error in errors:
            lines.append(f"- {error['section']}: {error['error']}")
    write_text(run_dir / "SUMMARY.md", "\n".join(lines) + "\n")
    if errors:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
