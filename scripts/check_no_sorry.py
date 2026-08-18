#!/usr/bin/env python3
"""Fail if any project source contains a real `sorry`.

Several files record retired or refuted statements verbatim inside comment
blocks, so comments are stripped before scanning.
"""

from __future__ import annotations

import pathlib
import re
import sys


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    found: list[str] = []
    for path in sorted((root / "AllenderOQ3").rglob("*.lean")):
        text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        for number, line in enumerate(text.splitlines(), start=1):
            line = re.sub(r"--.*", "", line)
            if re.search(r"\bsorry\b", line):
                found.append(f"{path.relative_to(root)}:{number}: {line.strip()}")
    if found:
        print("error: sorry found:", file=sys.stderr)
        for entry in found:
            print(f"  {entry}", file=sys.stderr)
        return 1
    print("sorry scan: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
