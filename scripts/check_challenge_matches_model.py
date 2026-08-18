#!/usr/bin/env python3
"""Check that Challenge.lean copies the project interface verbatim.

Comparator guarantees that `Solution.lean` proves the statement written in
`Challenge.lean`.  It cannot know that the definitions in `Challenge.lean` are
the ones the project itself uses, so this script compares them textually with
`AllenderOQ3/Model.lean` and `AllenderOQ3/Statement.lean` (doc comments and
blank lines ignored).
"""

from __future__ import annotations

import pathlib
import re
import sys

CHALLENGE_THEOREM = "theorem allender_oq3_challenge : AllenderOQ3Statement := by"


def significant_lines(text: str) -> list[str]:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    lines = [line.rstrip() for line in text.splitlines()]
    return [line for line in lines if line.strip() and line != "import Mathlib"]


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent

    challenge = significant_lines((root / "Challenge.lean").read_text())
    if CHALLENGE_THEOREM not in challenge:
        print("error: challenge theorem not found in Challenge.lean", file=sys.stderr)
        return 1
    challenge = challenge[: challenge.index(CHALLENGE_THEOREM)]

    model = significant_lines((root / "AllenderOQ3" / "Model.lean").read_text())

    if challenge != model:
        print(
            "error: Challenge.lean definitions differ from AllenderOQ3/Model.lean",
            file=sys.stderr,
        )
        for index, (left, right) in enumerate(zip(challenge, model)):
            if left != right:
                print(f"  first difference at definition line {index + 1}", file=sys.stderr)
                print(f"    Challenge.lean: {left}", file=sys.stderr)
                print(f"    Model.lean:     {right}", file=sys.stderr)
                break
        else:
            print(
                f"  lengths differ: {len(challenge)} vs {len(model)} lines",
                file=sys.stderr,
            )
        return 1

    print("challenge/model interface check: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
