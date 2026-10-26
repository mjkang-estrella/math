#!/usr/bin/env python3
"""Verify the full SHA-256 file inventory of an extracted release."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    expected = {}
    for line in (root / "SHA256SUMS").read_text().splitlines():
        checksum, relative = line.split("  ", 1)
        path = root / relative
        if not path.resolve().is_relative_to(root):
            raise SystemExit("Unsafe manifest path")
        expected[relative] = checksum
    missing_or_changed = [name for name, checksum in expected.items()
                          if not (root / name).is_file() or
                          hashlib.sha256((root / name).read_bytes()).hexdigest() != checksum]
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()
              and p.name != "SHA256SUMS"}
    extra = sorted(actual - expected.keys())
    status = "PASS" if not missing_or_changed and not extra else "FAIL"
    print(json.dumps({"status": status, "files": len(expected),
                      "missing_or_changed": missing_or_changed, "extra": extra}, indent=2))
    if status != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
