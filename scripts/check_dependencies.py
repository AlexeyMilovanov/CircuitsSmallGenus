#!/usr/bin/env python3
"""Verify that every Lake dependency is the clean revision pinned by the manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def git(repo: Path, *args: str) -> str:
    cp = subprocess.run(
        ["git", "-C", str(repo), *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if cp.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed for {repo}:\n{cp.stdout}")
    return cp.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--write-baseline", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    manifest_path = root / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages_dir = root / str(manifest.get("packagesDir") or ".lake/packages")
    failures: list[str] = []
    checked: list[str] = []
    for package in manifest.get("packages", []):
        name = str(package.get("name", ""))
        revision = package.get("rev")
        if not name or not revision:
            continue
        repo = packages_dir / name
        if repo.is_symlink() or not repo.is_dir():
            failures.append(f"{name}: missing, non-directory, or symlinked checkout: {repo}")
            continue
        try:
            head = git(repo, "rev-parse", "HEAD").strip()
            status = git(repo, "status", "--porcelain=v1", "--untracked-files=all")
        except RuntimeError as exc:
            failures.append(str(exc))
            continue
        if head != revision:
            failures.append(f"{name}: HEAD {head} != pinned {revision}")
        if status.strip():
            failures.append(f"{name}: dirty checkout:\n{status.rstrip()}")
        checked.append(name)
    digest = hashlib.sha256()
    if not packages_dir.exists():
        failures.append(f"missing packages tree: {packages_dir}")
    else:
        for directory, dirnames, filenames in os.walk(packages_dir, followlinks=False):
            base = Path(directory)
            traversable: list[str] = []
            for name in sorted(name for name in dirnames if name != ".git"):
                path = base / name
                rel = path.relative_to(packages_dir).as_posix()
                digest.update(rel.encode("utf-8"))
                digest.update(b"\0")
                if path.is_symlink():
                    digest.update(b"L\0")
                    digest.update(os.readlink(path).encode("utf-8"))
                    digest.update(b"\0")
                elif path.is_dir():
                    digest.update(b"D\0")
                    traversable.append(name)
                else:
                    failures.append(f"unsupported dependency directory entry: {path}")
            dirnames[:] = traversable
            for name in sorted(filenames):
                path = base / name
                rel = path.relative_to(packages_dir).as_posix()
                digest.update(rel.encode("utf-8"))
                digest.update(b"\0")
                if path.is_symlink():
                    digest.update(b"L\0")
                    digest.update(os.readlink(path).encode("utf-8"))
                    digest.update(b"\0")
                elif path.is_file():
                    digest.update(b"F\0")
                    with path.open("rb") as handle:
                        for chunk in iter(lambda: handle.read(4 * 1024 * 1024), b""):
                            digest.update(chunk)
                    digest.update(b"\0")
                else:
                    failures.append(f"unsupported dependency tree entry: {path}")
    actual_tree_digest = digest.hexdigest()
    baseline_path = root / "proof_loop/dependency_tree.sha256"
    if args.write_baseline:
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        baseline_path.write_text(actual_tree_digest + "\n", encoding="utf-8")
    elif not baseline_path.is_file() or baseline_path.is_symlink():
        failures.append(f"missing or unsafe dependency digest baseline: {baseline_path}")
    else:
        expected_tree_digest = baseline_path.read_text(encoding="utf-8").strip()
        if actual_tree_digest != expected_tree_digest:
            failures.append(
                "dependency tree digest mismatch: "
                f"{actual_tree_digest} != {expected_tree_digest}"
            )
    if failures:
        print("dependency integrity: FAIL", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    action = "WROTE BASELINE" if args.write_baseline else "PASS"
    print(
        f"dependency integrity: {action} "
        f"({len(checked)} pinned repositories, tree {actual_tree_digest})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
