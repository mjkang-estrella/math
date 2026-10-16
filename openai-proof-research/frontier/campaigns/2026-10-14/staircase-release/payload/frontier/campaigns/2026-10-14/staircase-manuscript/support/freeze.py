#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Freeze an inspected handoff and build a reading-copy-free public archive."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def entry(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def save(name, value):
    (ROOT / name).write_text(json.dumps(value, indent=2) + "\n")


def main():
    public = json.loads((ROOT / "public-files.json").read_text())["files"]
    assert len(public) == len(set(public)) and "public-manifest.json" not in public
    assert all(not path.startswith("inputs/") and ".." not in Path(path).parts for path in public)
    visual = json.loads((ROOT / "checks/visual-review.json").read_text())
    assert visual["status"] == "PASS"
    assert visual["pdf_sha256"] == entry("main.pdf")["sha256"]
    assert visual["pages_inspected"] == 6
    save("public-manifest.json", {"schema": 1, "rights": "RIGHTS.md",
         "excluded": ["inputs/**", "all external primary PDF and TXT reading copies", "internal review snapshots"],
         "self_hash_excluded": True, "files": [entry(path) for path in public]})
    with zipfile.ZipFile(ROOT / "staircase-manuscript-public.zip", "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in public + ["public-manifest.json"]:
            info = zipfile.ZipInfo(path, date_time=(2026, 10, 15, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / path).read_bytes())
    outputs = sorted(str(path.relative_to(ROOT)) for path in ROOT.rglob("*")
                     if path.is_file() and path.name not in ("output-manifest.json", "SHA256SUMS")
                     and "__pycache__" not in path.parts)
    save("output-manifest.json", {"schema": 1, "scope": "complete internal handoff, not a redistribution grant",
         "excluded_from_this_manifest": ["output-manifest.json", "SHA256SUMS", "__pycache__/**"],
         "files": [entry(path) for path in outputs]})
    (ROOT / "SHA256SUMS").write_text("".join(entry(path)["sha256"] + "  " + path + "\n"
                                         for path in outputs + ["output-manifest.json"]))
    print("Frozen:", len(public), "public payload files;", len(outputs), "internal handoff files")


if __name__ == "__main__":
    main()
