#!/usr/bin/env python3
"""Generate review-manifest.json for the r333 review lane.

Enumerates ALL files under the lane (including __pycache__ and hidden
files), excluding exactly, by relative path:
    review-manifest.json  (this manifest cannot hash itself)
    verify.py             (the verifier; hashed in the receipt instead)
    verification-receipt.json (written after verification)
Exit nonzero if any file is unreadable.
"""
import hashlib
import json
import os
import sys
from datetime import datetime, timezone

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCLUDED = {"review-manifest.json", "verify.py", "verification-receipt.json"}


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    files = []
    for dirpath, dirnames, filenames in os.walk(LANE):
        for name in sorted(filenames):
            p = os.path.join(dirpath, name)
            rel = os.path.relpath(p, LANE)
            if rel in EXCLUDED:
                continue
            st = os.stat(p)
            files.append({"path": rel, "bytes": st.st_size,
                          "sha256": sha256_file(p)})
    files.sort(key=lambda e: e["path"])
    manifest = {
        "lane": "pi-cayley-avoidance-preliminary-review-r333",
        "generated_at_utc": datetime.now(timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ"),
        "excluded_by_exact_relative_name": sorted(EXCLUDED),
        "files": files,
    }
    out = os.path.join(LANE, "review-manifest.json")
    with open(out, "w") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
    print(json.dumps({"files": len(files), "out": out}, indent=1))


if __name__ == "__main__":
    main()
