"""Read-only verifier. Detached hashes must be supplied explicitly by the caller."""
import argparse
import hashlib
import json
import os
import re
import stat
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(condition, message):
    if not condition:
        raise ValueError(message)


def regular(path):
    st = path.lstat()
    check(stat.S_ISREG(st.st_mode), f"not a regular file: {path.name}")
    return st


def inventory(directory, prefix):
    result = set()
    check(stat.S_ISDIR(directory.lstat().st_mode), "packet is not a real directory")
    for entry in os.scandir(directory):
        child = Path(entry.path)
        rel = prefix + "/" + entry.name
        st = child.lstat()
        check(not stat.S_ISLNK(st.st_mode), "symlink in packet")
        if stat.S_ISDIR(st.st_mode):
            result.update(inventory(child, rel))
        else:
            check(stat.S_ISREG(st.st_mode), "special file in packet")
            result.add(rel)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    args = ap.parse_args()
    for key in ("final_sha256", "manifest_sha256", "report_sha256"):
        check(re.fullmatch(r"[0-9a-f]{64}", getattr(args, key)) is not None,
              "each detached anchor must be an explicit lowercase SHA256")
    root = Path(args.root)
    check(stat.S_ISDIR(root.lstat().st_mode), "root is not a real directory")
    manifest_path = root / "MANIFEST.json"
    report_path = root / "REPORT.md"
    regular(manifest_path)
    regular(report_path)
    manifest_bytes = manifest_path.read_bytes()
    check(digest(manifest_bytes) == args.manifest_sha256, "manifest anchor mismatch")
    check(digest(report_path.read_bytes()) == args.report_sha256, "outside report anchor mismatch")
    manifest = json.loads(manifest_bytes)
    check(manifest["schema"] == "source364-r239-packet-v1", "unexpected manifest schema")
    expected = set()
    for row in manifest["files"]:
        rel = row["path"]
        p = PurePosixPath(rel)
        check(p.as_posix() == rel and not p.is_absolute() and
              ".." not in p.parts and len(p.parts) >= 2 and p.parts[0] == "packet",
              "invalid selected path")
        check(rel not in expected, "duplicate selected path")
        expected.add(rel)
        st = regular(root / rel)
        check(stat.S_IMODE(st.st_mode) == int(row["mode"], 8), "selected mode mismatch: " + rel)
        data = (root / rel).read_bytes()
        check(len(data) == row["bytes"], "selected size mismatch: " + rel)
        check(digest(data) == row["sha256"], "selected hash mismatch: " + rel)
    check(inventory(root / "packet", "packet") == expected, "exact selection mismatch")
    check("packet/FINAL.md" in expected, "FINAL is not selected")
    check(digest((root / "packet/FINAL.md").read_bytes()) == args.final_sha256,
          "FINAL detached anchor mismatch")
    print(json.dumps({"artifact_verification": "PASS", "selected_files": len(expected),
                      "mathematical_grade": "not assessed"}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        raise SystemExit("FAIL: " + str(exc))
