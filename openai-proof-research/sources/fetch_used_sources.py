"""Fetch or verify the exact upstream source files used by accepted findings.

Run: python openai-proof-research/sources/fetch_used_sources.py [--verify-only]
Downloads are cached and ignored by git. No third-party packages required.
"""
import argparse
import hashlib
import json
from pathlib import Path
import urllib.request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "used-sources.json").read_text())
    commit = manifest["commit"]
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe source path: {relative}")
        target = root / "cache" / "verified" / relative
        if not target.exists() and not args.verify_only:
            url = f"https://raw.githubusercontent.com/openai/math/{commit}/{relative.as_posix()}"
            data = urllib.request.urlopen(url, timeout=60).read()
            if hashlib.sha256(data).hexdigest() != entry["sha256"]:
                raise ValueError(f"Downloaded source hash mismatch: {relative}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        data = target.read_bytes()
        if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError(f"Cached source hash mismatch: {relative}")
    print(f"Verified {len(manifest['files'])} source files at {commit}.")


if __name__ == "__main__":
    main()
