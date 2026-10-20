#!/usr/bin/env python3
"""Fetch pinned family-184 TeX sources from raw GitHub and authenticate them by Git blob SHA-1.

Writes only below <root>/packet/private/source and <root>/packet/private/source/receipts.json.
"""
import hashlib, json, sys, urllib.request
from pathlib import Path

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
PREFIXES = (
    "preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026/",
    "preprints/Correspondence-Coloring-Graphs-with-a-Forbidden-Clique-October-5-2026/",
)


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main():
    root, project = Path(sys.argv[1]), Path(sys.argv[2])
    tree = json.loads((project / "sources/preprints-tree.json").read_bytes())
    assert tree["truncated"] is False and len(tree["tree"]) == 13223
    out = root / "packet/private/source"
    receipts = []
    for e in tree["tree"]:
        p = e["path"]
        if e["type"] != "blob" or not p.startswith(PREFIXES) or p.endswith(".pdf"):
            continue
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{p}"
        data = urllib.request.urlopen(url, timeout=60).read()
        ok = blob_sha(data) == e["sha"]
        if not ok:
            raise SystemExit(f"blob mismatch {p}")
        dest = out / p
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        receipts.append({"path": p, "url": url, "git_blob_sha1": e["sha"],
                         "sha256": hashlib.sha256(data).hexdigest(), "size": len(data)})
    (out / "receipts.json").write_text(json.dumps({"pin": PIN, "files": receipts}, indent=1) + "\n")
    print(f"fetched and authenticated {len(receipts)} files")


if __name__ == "__main__":
    main()
