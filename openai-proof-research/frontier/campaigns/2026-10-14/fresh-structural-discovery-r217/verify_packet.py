"""Read-only exact packet verification; explicit external anchors required."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat

RESERVED = {"MANIFEST.json", "DETACHED.json", "REPORT.md"}
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def listing(root):
    files, dirs = {}, {}
    for base, dn, fn in os.walk(root, topdown=True, followlinks=False):
        bp = Path(base); rel = bp.relative_to(root).as_posix()
        if rel == ".": dn[:] = [n for n in dn if n != "controls"]
        assert not bp.is_symlink(), "symlink directory"
        dirs[rel] = format(stat.S_IMODE(bp.stat().st_mode), "04o")
        for n in dn: assert not (bp/n).is_symlink(), "symlink directory"
        for n in fn:
            p = bp/n; q = p.relative_to(root).as_posix()
            if q in RESERVED: continue
            assert not p.is_symlink() and p.is_file(), "nonregular member"
            files[q] = p
    return files, dirs

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    for name, anchor in [("FINAL.md", final_sha), ("MANIFEST.json", manifest_sha), ("REPORT.md", report_sha)]:
        assert len(anchor) == 64 and all(c in "0123456789abcdef" for c in anchor), "invalid explicit anchor"
        p = root/name
        assert not p.is_symlink() and p.is_file(), "nonregular anchor"
        assert digest(p) == anchor, "detached anchor mismatch: " + name
    m = json.loads((root/"MANIFEST.json").read_text())
    assert m["format"] == "r217-exact-selection-v1"
    actual, dirs = listing(root)
    expected = {}
    for row in m["files"]:
        q = row["path"]; p = PurePosixPath(q)
        assert not p.is_absolute() and ".." not in p.parts and q == p.as_posix(), "unsafe member"
        assert q not in RESERVED and p.parts[0] != "controls", "reserved member"
        assert q not in expected, "duplicate member"
        expected[q] = row
    assert set(actual) == set(expected), "exact file selection mismatch"
    assert dirs == m["directories"], "exact directory selection/mode mismatch"
    assert "FINAL.md" in expected and expected["FINAL.md"]["sha256"] == final_sha
    for q, p in actual.items():
        row = expected[q]; st = p.stat()
        assert stat.S_IMODE(st.st_mode) == int(row["mode"], 8), "mode mismatch: " + q
        assert st.st_size == row["bytes"], "length mismatch: " + q
        assert digest(p) == row["sha256"], "content mismatch: " + q
    return {"artifact_integrity": "verified", "files": len(actual), "directories": len(dirs), "mathematical_gate": False}

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--root", required=True)
    p.add_argument("--final-sha256", required=True)
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--report-sha256", required=True)
    a = p.parse_args()
    print(json.dumps(verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256), sort_keys=True))
