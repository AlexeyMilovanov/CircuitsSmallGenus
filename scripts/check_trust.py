#!/usr/bin/env python3
"""Audit the OQ3 trust boundary without being fooled by comments or strings."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = Path("AllenderOQ3/ExternalFacts.lean")
TARGET = Path("AllenderOQ3/Target.lean")
INTERNAL_PREFIX = "AllenderOQ3/Internal/"
COMPARATOR_CHALLENGE = Path("Challenge.lean")
FROZEN_MANIFEST = Path("proof_loop/frozen_api.sha256")

EXPECTED_EXTERNAL = (
    "hansenArcOrder",
    "quantitativeCylindricalACC",
)


def strip_comments_and_strings(text: str) -> str:
    """Replace Lean comments and string contents by spaces, preserving lines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        two = text[i : i + 2]
        ch = text[i]
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if two == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif two == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if two == "--":
            in_line = True
            out.extend("  ")
            i += 2
        elif two == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def lean_files(root: Path) -> list[Path]:
    result: list[Path] = []
    for path in root.rglob("*.lean"):
        rel = path.relative_to(root).as_posix()
        if rel.startswith(".lake/") or rel.startswith("proof_loop_runs/"):
            continue
        result.append(path)
    return sorted(result)


def token_locations(code: str, token: str) -> list[int]:
    return [code.count("\n", 0, match.start()) + 1
            for match in re.finditer(rf"\b{re.escape(token)}\b", code)]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    digest.update(path.read_bytes())
    return digest.hexdigest()


def audit(root: Path, release: bool, require_no_external: bool = False) -> dict[str, object]:
    errors: list[str] = []
    external_sorries: list[str] = []
    internal_sorries: list[str] = []
    challenge_sorries: list[str] = []

    for path in lean_files(root):
        rel = path.relative_to(root).as_posix()
        code = strip_comments_and_strings(path.read_text(encoding="utf-8"))

        for forbidden in (
            "axiom", "constant", "opaque", "admit", "sorryAx", "unsafe",
            "implemented_by", "native_decide",
        ):
            for line in token_locations(code, forbidden):
                errors.append(f"forbidden token {forbidden}: {rel}:{line}")

        for line in token_locations(code, "sorry"):
            location = f"{rel}:{line}"
            if rel == EXTERNAL.as_posix():
                external_sorries.append(location)
            elif rel == TARGET.as_posix() or rel.startswith(INTERNAL_PREFIX):
                internal_sorries.append(location)
            elif rel == COMPARATOR_CHALLENGE.as_posix():
                challenge_sorries.append(location)
            else:
                errors.append(f"sorry outside the permitted files: {location}")

    challenge_code = strip_comments_and_strings(
        (root / COMPARATOR_CHALLENGE).read_text(encoding="utf-8")
    )
    challenge_body = re.search(
        r"theorem\s+allender_oq3_challenge\s*:\s*"
        r"AllenderOQ3Statement\s*:=\s*by\s+sorry\b",
        challenge_code,
        flags=re.DOTALL,
    )
    if len(challenge_sorries) != 1 or challenge_body is None:
        errors.append(
            "Challenge.lean must contain exactly the comparator's one theorem placeholder"
        )

    external_path = root / EXTERNAL
    external_code = strip_comments_and_strings(external_path.read_text(encoding="utf-8"))
    open_expected: list[str] = []
    theorem_starts = list(re.finditer(r"\btheorem\s+([A-Za-z0-9_']+)\b", external_code))
    theorem_blocks: dict[str, str] = {}
    for index, match in enumerate(theorem_starts):
        stop = theorem_starts[index + 1].start() if index + 1 < len(theorem_starts) else len(external_code)
        theorem_blocks[match.group(1)] = external_code[match.start():stop]
    for name in EXPECTED_EXTERNAL:
        block = theorem_blocks.get(name)
        if block is None or not re.search(rf"theorem\s+{name}\b.*?:=.*?\bby\b", block, flags=re.DOTALL):
            errors.append(f"missing external theorem declaration for {name}")
            continue
        if re.search(r"\bby\s+sorry\b", block):
            open_expected.append(name)
    if len(external_sorries) != len(open_expected):
        errors.append(
            "sorry in ExternalFacts.lean is not exactly one of the two actionable theorem bodies"
        )
    if len(external_sorries) > len(EXPECTED_EXTERNAL):
        errors.append(f"expected at most 2 actionable external sorries, found {len(external_sorries)}")

    target_code = strip_comments_and_strings((root / TARGET).read_text(encoding="utf-8"))
    if not re.search(
        r"theorem\s+turing_candidate_000003_of_principles\s*:\s*"
        r"AllenderOQ3ConditionalStatement\s*:=",
        target_code,
        flags=re.DOTALL,
    ):
        errors.append("conditional target statement changed")
    if not re.search(
        r"theorem\s+turing_candidate_000003\s*:\s*AllenderOQ3Statement\s*:=",
        target_code,
        flags=re.DOTALL,
    ):
        errors.append("final target statement changed")
    final_wrapper = (
        r"theorem\s+turing_candidate_000003\s*:\s*AllenderOQ3Statement\s*:=\s*"
        r"turing_candidate_000003_of_principles\s*"
        r"AllenderOQ3\.External\.rotationZeroPlanarity\s*"
        r"AllenderOQ3\.External\.hansenArcOrder\s*"
        r"AllenderOQ3\.External\.quantitativeCylindricalACC\b"
    )
    if not re.search(final_wrapper, target_code, flags=re.DOTALL):
        errors.append("final target must apply one proved principle and exactly two frozen external facts")

    manifest_path = root / FROZEN_MANIFEST
    if not manifest_path.exists():
        errors.append(f"missing frozen API manifest: {FROZEN_MANIFEST}")
    else:
        for raw in manifest_path.read_text(encoding="utf-8").splitlines():
            raw = raw.strip()
            if not raw or raw.startswith("#"):
                continue
            expected, rel = raw.split(maxsplit=1)
            path = root / rel
            if not path.exists():
                errors.append(f"frozen API file missing: {rel}")
            elif sha256(path) != expected:
                errors.append(f"frozen API checksum mismatch: {rel}")

    if release and internal_sorries:
        errors.append(
            "release audit requires zero internal sorries: "
            + ", ".join(internal_sorries)
        )
    if require_no_external and external_sorries:
        errors.append(
            "final audit requires both external facts to be proved: "
            + ", ".join(external_sorries)
        )

    return {
        "ok": not errors,
        "release": release,
        "require_no_external": require_no_external,
        "external_sorries": external_sorries,
        "internal_sorries": internal_sorries,
        "challenge_sorries": challenge_sorries,
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--release", action="store_true")
    parser.add_argument("--require-no-external", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = audit(args.root.resolve(), args.release, args.require_no_external)
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print("trust audit:", "PASS" if report["ok"] else "FAIL")
        print("actionable external sorries:", len(report["external_sorries"]))
        print("supporting internal sorries:", len(report["internal_sorries"]))
        for error in report["errors"]:
            print("ERROR:", error)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
