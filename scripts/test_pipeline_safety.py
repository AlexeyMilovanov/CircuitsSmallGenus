#!/usr/bin/env python3
"""No-network regression tests for the OQ3 proof conveyor."""

from __future__ import annotations

import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "oq3_pipeline", ROOT / "scripts/run_proof_pipeline.py"
)
assert SPEC is not None and SPEC.loader is not None
PIPELINE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PIPELINE)

PROJECT_ID = "447e1c5c-d526-4901-b33a-1296636bc98b"
TASK_ID = "dbb3763b-debb-4bae-abb8-2ca9a1fce63c"


def write_executable(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def test_aristotle_submit_once_and_resume() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        state = root / "fake_state"
        state.mkdir()
        os.environ["OQ3_FAKE_STATE"] = str(state)
        fake = root / "aristotle"
        write_executable(
            fake,
            f'''#!/usr/bin/env python3
import io, os, pathlib, sys, tarfile
state = pathlib.Path(os.environ["OQ3_FAKE_STATE"])
cmd = sys.argv[1]
if cmd == "tasks":
    mode = (state / "mode").read_text().strip() if (state / "mode").exists() else "complete"
    status = {{"inprogress": "IN_PROGRESS", "failed": "FAILED"}}.get(mode, "COMPLETE")
    print("{TASK_ID}  synthetic  " + status)
    raise SystemExit(0)
if cmd == "download":
    destination = pathlib.Path(sys.argv[sys.argv.index("--destination") + 1])
    data = b'name = "fake"\\nversion = "0.1.0"\\n'
    with tarfile.open(destination, "w:gz") as tf:
        info = tarfile.TarInfo("fake/lakefile.toml")
        info.size = len(data)
        tf.addfile(info, io.BytesIO(data))
    raise SystemExit(0)
raise SystemExit(2)
''',
        )
        PIPELINE.ARISTOTLE_BIN = fake
        iteration = root / "iteration"
        iteration.mkdir()
        submit_count = state / "submit_count"
        write_executable(
            iteration / "submit_aristotle.py",
            f'''#!/usr/bin/env python3
from pathlib import Path
p = Path({str(submit_count)!r})
n = int(p.read_text()) if p.exists() else 0
p.write_text(str(n + 1))
print("Project created: {PROJECT_ID}")
''',
        )

        first = PIPELINE.submit_aristotle(iteration, timeout_seconds=2)
        assert first["returncode"] == 0, first
        assert submit_count.read_text() == "1"
        persisted = json.loads((iteration / "aristotle_state.json").read_text())
        assert persisted["project_id"] == PROJECT_ID
        assert persisted["task_id"] == TASK_ID
        assert (iteration / "aristotle_result.tar.gz").is_file()

        (iteration / "aristotle_result.tar.gz").unlink()
        second = PIPELINE.submit_aristotle(iteration, timeout_seconds=2)
        assert second["returncode"] == 0, second
        assert second.get("resumed") is True
        assert submit_count.read_text() == "1"

        (iteration / "aristotle_result.tar.gz").unlink()
        (state / "mode").write_text("inprogress")
        third = PIPELINE.submit_aristotle(iteration, timeout_seconds=0)
        assert third["followup"]["reason"] == "timeout_waiting_for_aristotle"
        assert submit_count.read_text() == "1"

        (state / "mode").write_text("failed")
        failed_first = PIPELINE.submit_aristotle(iteration, timeout_seconds=2)
        assert failed_first["followup"]["reason"] == "aristotle_terminal_failure"
        assert not (iteration / "aristotle_result.tar.gz").exists()
        failed_second = PIPELINE.submit_aristotle(iteration, timeout_seconds=2)
        assert failed_second["followup"]["reason"] == "aristotle_terminal_failure"
        assert submit_count.read_text() == "1"

        ambiguous = root / "ambiguous"
        ambiguous.mkdir()
        ambiguous_count = state / "ambiguous_count"
        write_executable(
            ambiguous / "submit_aristotle.py",
            f'''#!/usr/bin/env python3
from pathlib import Path
p = Path({str(ambiguous_count)!r})
n = int(p.read_text()) if p.exists() else 0
p.write_text(str(n + 1))
print("connection closed before id")
''',
        )
        fourth = PIPELINE.submit_aristotle(ambiguous, timeout_seconds=2)
        assert fourth["reason"] == "ambiguous_aristotle_submission_without_id"
        fifth = PIPELINE.submit_aristotle(ambiguous, timeout_seconds=2)
        assert fifth["reason"] == "ambiguous_aristotle_submission_without_id"
        assert ambiguous_count.read_text() == "1"

        interrupted = root / "interrupted"
        interrupted.mkdir()
        interrupted_count = state / "interrupted_count"
        write_executable(
            interrupted / "submit_aristotle.py",
            f'''#!/usr/bin/env python3
from pathlib import Path
p = Path({str(interrupted_count)!r})
n = int(p.read_text()) if p.exists() else 0
p.write_text(str(n + 1))
print("this command must never run while the intent guard exists")
''',
        )
        (interrupted / "aristotle_state.json").write_text(json.dumps({
            "submission_status": "submitting_unknown_outcome",
            "automatic_resubmit_forbidden": True,
            "attempt_started_at": "synthetic-crash-window",
        }))
        sixth = PIPELINE.submit_aristotle(interrupted, timeout_seconds=2)
        assert sixth["reason"] == "ambiguous_aristotle_submission_without_id"
        assert not interrupted_count.exists()

        malformed = root / "malformed"
        malformed.mkdir()
        malformed_count = state / "malformed_count"
        write_executable(
            malformed / "submit_aristotle.py",
            f'''#!/usr/bin/env python3
from pathlib import Path
Path({str(malformed_count)!r}).write_text("called")
''',
        )
        (malformed / "aristotle_state.json").write_text("{{not-json", encoding="utf-8")
        seventh = PIPELINE.submit_aristotle(malformed, timeout_seconds=2)
        assert seventh["reason"] == "ambiguous_aristotle_submission_without_id"
        assert not malformed_count.exists()

        (malformed / "aristotle_state.json").write_text(
            json.dumps({"foo": 1}), encoding="utf-8"
        )
        seventh_b = PIPELINE.submit_aristotle(malformed, timeout_seconds=2)
        assert seventh_b["reason"] == "ambiguous_aristotle_submission_without_id"
        assert not malformed_count.exists()

        forged = root / "forged"
        forged.mkdir()
        forged_count = state / "forged_count"
        write_executable(
            forged / "submit_aristotle.py",
            f'''#!/usr/bin/env python3
from pathlib import Path
Path({str(forged_count)!r}).write_text("called")
''',
        )
        with tarfile.open(forged / "aristotle_result.tar.gz", "w:gz") as tf:
            data = b'name = "forged"\nversion = "0.1.0"\n'
            info = tarfile.TarInfo("forged/lakefile.toml")
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
        eighth = PIPELINE.submit_aristotle(forged, timeout_seconds=2)
        assert eighth["reason"] == "untrusted_preexisting_aristotle_archive"
        assert not forged_count.exists()


def test_safe_tar_rejects_links() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        archive = root / "bad.tar.gz"
        with tarfile.open(archive, "w:gz") as tf:
            link = tarfile.TarInfo("project/escape")
            link.type = tarfile.SYMTYPE
            link.linkname = "/tmp/escape"
            tf.addfile(link)
        try:
            PIPELINE.safe_extract_project_tar(archive, root / "out")
        except RuntimeError as exc:
            assert "unsupported tar member type" in str(exc)
        else:
            raise AssertionError("symlink archive was accepted")


def test_canonical_symlink_restoration_and_recovery_rejection() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        old_root = PIPELINE.ROOT
        old_snapshot = dict(PIPELINE.CANONICAL_TREE_SNAPSHOT)
        try:
            PIPELINE.ROOT = root
            source = root / "AllenderOQ3/Model.lean"
            source.parent.mkdir(parents=True)
            source.write_text("frozen bytes\n", encoding="utf-8")
            PIPELINE.capture_canonical_tree_snapshot()

            outside = root / "outside"
            outside.write_text("outside\n", encoding="utf-8")
            source.unlink()
            source.symlink_to(outside)
            extra = root / "unexpected-link"
            extra.symlink_to(outside)
            changed = PIPELINE.restore_unexpected_canonical_changes()
            assert "AllenderOQ3/Model.lean" in changed
            assert "unexpected-link" in changed
            assert source.is_file() and not source.is_symlink()
            assert source.read_text(encoding="utf-8") == "frozen bytes\n"
            assert not os.path.lexists(extra)

            target = root / "AllenderOQ3/Internal/New.lean"
            target.parent.mkdir(parents=True)
            target.symlink_to(outside)
            journal = root / "proof_loop/MERGE_JOURNAL.json"
            journal.parent.mkdir(parents=True)
            journal.write_text(json.dumps({"entries": [{
                "rel": "AllenderOQ3/Internal/New.lean",
                "existed": False,
            }]}), encoding="utf-8")
            try:
                PIPELINE.recover_incomplete_merge()
            except RuntimeError as exc:
                assert "symlinked project target" in str(exc)
            else:
                raise AssertionError("merge recovery accepted a symlink target")

            journal.unlink()
            journal.write_text("{broken", encoding="utf-8")
            try:
                PIPELINE.recover_incomplete_merge()
            except RuntimeError as exc:
                assert "invalid merge recovery journal JSON" in str(exc)
            else:
                raise AssertionError("merge recovery discarded malformed JSON")
            assert journal.exists()

            journal.write_text(json.dumps({"entries": [{
                "rel": "AllenderOQ3/Internal/New.lean",
            }]}), encoding="utf-8")
            try:
                PIPELINE.recover_incomplete_merge()
            except RuntimeError as exc:
                assert "requires rel and Boolean existed" in str(exc)
            else:
                raise AssertionError("merge recovery accepted an entry without existed")
            assert journal.exists()

            journal.write_text(json.dumps({"entries": []}), encoding="utf-8")
            try:
                PIPELINE.recover_incomplete_merge()
            except RuntimeError as exc:
                assert "invalid merge recovery journal" in str(exc)
            else:
                raise AssertionError("merge recovery discarded an empty journal")
            assert journal.exists()
        finally:
            PIPELINE.ROOT = old_root
            PIPELINE.CANONICAL_TREE_SNAPSHOT.clear()
            PIPELINE.CANONICAL_TREE_SNAPSHOT.update(old_snapshot)


def test_strategy_cadence() -> None:
    strategic = {
        i for i in range(1, 13)
        if i >= 1 and (i - 1) % 5 == 0
    }
    assert strategic == {1, 6, 11}
    assert {
        "blocked_agent_control_file_change",
        "blocked_canonical_dependency_change",
    } <= PIPELINE.BLOCKING_STATUSES
    assert {
        "blocked_stage_failure",
        "blocked_stage_audit_failure",
        "blocked_trust_boundary_change",
        "blocked_aristotle_result_failure",
        "blocked_aristotle_terminal_status",
        "blocked_missing_aristotle_result",
    }.isdisjoint(PIPELINE.BLOCKING_STATUSES)


def test_failed_audit_becomes_repair_context() -> None:
    with tempfile.TemporaryDirectory() as raw:
        section = Path(raw)
        failed = section / "iter_005_proof"
        failed.mkdir()
        (failed / "manifest.json").write_text(
            json.dumps({
                "iteration": 5,
                "status": "complete",
                "stages": [{
                    "stage": "01_gemini",
                    "ok": True,
                    "audit_rc": 1,
                    "completed": True,
                    "verified": False,
                }],
            }),
            encoding="utf-8",
        )
        (failed / "01_gemini.audit.md").write_text(
            "error: synthetic Lean failure\n", encoding="utf-8"
        )
        context = PIPELINE.latest_repair_context(section, 6)
        assert "iter_005_proof" in context
        assert "synthetic Lean failure" in context


def test_global_runner_lock_is_exclusive() -> None:
    with tempfile.TemporaryDirectory() as raw:
        old_dir = PIPELINE.PROOF_LOOP_DIR
        old_handle = PIPELINE.RUNNER_LOCK_HANDLE
        first_handle = None
        try:
            PIPELINE.PROOF_LOOP_DIR = Path(raw)
            PIPELINE.RUNNER_LOCK_HANDLE = None
            PIPELINE.acquire_runner_lock()
            first_handle = PIPELINE.RUNNER_LOCK_HANDLE
            try:
                PIPELINE.acquire_runner_lock()
            except RuntimeError as exc:
                assert "already holds RUNNER.lock" in str(exc)
            else:
                raise AssertionError("a second runner acquired the global lock")
        finally:
            if first_handle is not None:
                PIPELINE.fcntl.flock(first_handle.fileno(), PIPELINE.fcntl.LOCK_UN)
                first_handle.close()
            PIPELINE.PROOF_LOOP_DIR = old_dir
            PIPELINE.RUNNER_LOCK_HANDLE = old_handle


if __name__ == "__main__":
    if os.name == "posix":
        test_aristotle_submit_once_and_resume()
        test_canonical_symlink_restoration_and_recovery_rejection()
        test_global_runner_lock_is_exclusive()
    test_safe_tar_rejects_links()
    test_strategy_cadence()
    test_failed_audit_becomes_repair_context()
    print("pipeline safety tests: PASS")
