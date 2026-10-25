"""Read-only exact-selection verifier. Never writes, repairs, or follows symlinks."""
import argparse, hashlib, json, stat
from pathlib import Path, PurePosixPath

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def mode(p):
    return f"{stat.S_IMODE(p.stat().st_mode):04o}"

def safe_name(s):
    p=PurePosixPath(s)
    assert s and not p.is_absolute() and str(p)==s and all(x not in (".","..") for x in p.parts), "unsafe manifest path"
    return s

def main():
    ap=argparse.ArgumentParser()
    for flag in ("packet","manifest-sha256","final-sha256","report","report-sha256"):
        ap.add_argument("--"+flag,required=True)
    args=ap.parse_args()
    root=Path(args.packet); report=Path(args.report)
    assert root.is_dir() and not root.is_symlink(), "packet root type"
    mf=root/"MANIFEST.json"
    assert mf.is_file() and not mf.is_symlink(), "manifest type"
    assert sha(mf)==args.manifest_sha256, "detached manifest hash"
    assert mode(mf)=="0444", "manifest mode"
    m=json.loads(mf.read_bytes())
    assert m["schema"]=="s238-independent-correctness-selection-v1", "schema"
    fs=m["files"]; ds=m["directories"]
    names=[safe_name(x["path"]) for x in fs]
    assert len(names)==len(set(names)) and "MANIFEST.json" not in names, "file names"
    dnames=[x["path"] for x in ds]
    assert len(dnames)==len(set(dnames)) and "." in dnames, "directory names"
    for s in dnames:
        if s!=".": safe_name(s)
    actual_files=set();actual_dirs={"."}
    for p in root.rglob("*"):
        assert not p.is_symlink(), "symlink in packet"
        rel=p.relative_to(root).as_posix()
        if p.is_dir():actual_dirs.add(rel)
        else:
            assert p.is_file(), "special file in packet"
            actual_files.add(rel)
    assert actual_files==set(names)|{"MANIFEST.json"}, "exact file selection"
    assert actual_dirs==set(dnames), "exact directory selection"
    for e in fs:
        p=root/e["path"]
        assert p.stat().st_size==e["bytes"] and sha(p)==e["sha256"], "file bytes/hash: "+e["path"]
        assert mode(p)==e["mode"], "file mode: "+e["path"]
    for e in ds:
        p=root if e["path"]=="." else root/e["path"]
        assert mode(p)==e["mode"], "directory mode: "+e["path"]
    assert "FINAL.md" in names and sha(root/"FINAL.md")==args.final_sha256, "detached final hash"
    assert report.is_file() and not report.is_symlink(), "report type"
    assert sha(report)==args.report_sha256 and mode(report)=="0444", "detached report hash/mode"
    print(json.dumps({"verified":True,"files":len(fs),"directories":len(ds),"manifest_sha256":args.manifest_sha256,"final_sha256":args.final_sha256,"report_sha256":args.report_sha256,"read_only":True},sort_keys=True))

if __name__=="__main__":
    main()
