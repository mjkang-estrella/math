#!/usr/bin/env python3
"""Read-only exact-selection/mode verification. Detached anchors are mandatory."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

def digest(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for block in iter(lambda:f.read(65536),b""): h.update(block)
    return h.hexdigest()

def mode(p): return format(stat.S_IMODE(p.stat().st_mode),"04o")
def require(test,why):
    if not test: raise ValueError(why)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--packet",required=True,type=Path)
    ap.add_argument("--final-sha256",required=True)
    ap.add_argument("--manifest-sha256",required=True)
    ap.add_argument("--report",required=True,type=Path)
    ap.add_argument("--report-sha256",required=True)
    a=ap.parse_args(); p=a.packet
    for anchor in [a.final_sha256,a.manifest_sha256,a.report_sha256]:
        require(len(anchor)==64 and all(c in "0123456789abcdef" for c in anchor),"invalid detached SHA256")
    require(p.is_dir() and not p.is_symlink(),"packet is not an ordinary directory")
    for path,wanted in [(p/"FINAL.md",a.final_sha256),(p/"MANIFEST.json",a.manifest_sha256),(a.report,a.report_sha256)]:
        require(path.is_file() and not path.is_symlink(),"anchor target missing or symlink: "+str(path))
        require(mode(path)=="0600","anchor target mode mismatch: "+str(path))
        require(digest(path)==wanted,"detached anchor mismatch: "+str(path))
    manifest=json.loads((p/"MANIFEST.json").read_bytes())
    require(manifest.get("format")=="r245-exact-selection-v1","manifest format mismatch")
    files=manifest["files"]; directories=manifest["directories"]
    require("FINAL.md" in files and "MANIFEST.json" not in files,"invalid manifest selection")
    for rel in list(files)+list(directories):
        require(not Path(rel).is_absolute() and ".." not in Path(rel).parts and "\\" not in rel,"unsafe selected path")
    seen_files=set();seen_dirs={"."}
    for here,ds,fs in os.walk(p,topdown=True,followlinks=False):
        for name in ds+fs:
            path=Path(here)/name
            require(not path.is_symlink(),"symlink in packet: "+str(path.relative_to(p)))
        for name in ds:seen_dirs.add((Path(here)/name).relative_to(p).as_posix())
        for name in fs:seen_files.add((Path(here)/name).relative_to(p).as_posix())
    require(seen_files==set(files)|{"MANIFEST.json"},"exact file selection mismatch")
    require(seen_dirs==set(directories),"exact directory selection mismatch")
    for rel,wanted in directories.items():require(mode(p/rel)==wanted,"directory mode mismatch: "+rel)
    for rel,entry in files.items():
        path=p/rel
        require(path.is_file(),"nonregular selected entry: "+rel)
        require(mode(path)==entry["mode"],"file mode mismatch: "+rel)
        require(path.stat().st_size==entry["bytes"],"file size mismatch: "+rel)
        require(digest(path)==entry["sha256"],"file digest mismatch: "+rel)
    print("Exact selection, bytes, modes, and all three detached anchors verified; artifact check only.")

if __name__=="__main__":
    try:main()
    except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:
        print("FAIL: "+str(e),file=sys.stderr);sys.exit(2)
