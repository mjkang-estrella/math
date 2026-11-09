#!/usr/bin/env python3
"""Read-only exact packet verification; caller must supply all detached anchors."""
import argparse, hashlib, json, os, re, sys
from pathlib import Path, PurePosixPath

def digest(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1048576),b""): h.update(b)
    return h.hexdigest()

def verify(root, final_hash, manifest_hash, report_hash):
    for name, anchor in [("FINAL.md",final_hash),("MANIFEST.json",manifest_hash),("REPORT.md",report_hash)]:
        if not re.fullmatch(r"[0-9a-f]{64}",anchor): raise ValueError("invalid explicit anchor")
        p=root/name
        if p.is_symlink() or not p.is_file() or digest(p)!=anchor: raise ValueError("anchor mismatch: "+name)
    m=json.loads((root/"MANIFEST.json").read_text())
    if m.get("version")!=1 or not isinstance(m.get("files"),list): raise ValueError("manifest schema")
    expected={}
    for e in m["files"]:
        s=e["path"]; p=PurePosixPath(s)
        if p.is_absolute() or ".." in p.parts or not p.parts or p.parts[0]!="packet" or str(p)!=s or "\\" in s:
            raise ValueError("unsafe packet path")
        if s in expected: raise ValueError("duplicate packet path")
        expected[s]=e
    packet=root/"packet"
    if packet.is_symlink() or not packet.is_dir(): raise ValueError("invalid packet root")
    actual=set()
    for base,dirs,files in os.walk(packet,followlinks=False):
        for name in dirs+files:
            if (Path(base)/name).is_symlink(): raise ValueError("symlink in packet")
        for name in files: actual.add((Path(base)/name).relative_to(root).as_posix())
    if actual!=set(expected): raise ValueError("exact packet membership mismatch")
    for s,e in expected.items():
        p=root/s
        if not p.is_file() or p.stat().st_size!=e["bytes"] or digest(p)!=e["sha256"]:
            raise ValueError("packet bytes mismatch: "+s)
    return len(expected)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,required=True)
    p.add_argument("--final-sha256",required=True)
    p.add_argument("--manifest-sha256",required=True)
    p.add_argument("--report-sha256",required=True)
    a=p.parse_args()
    try:
        n=verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256)
    except (ValueError,KeyError,OSError,TypeError,json.JSONDecodeError) as e:
        print("REJECTED:",e); return 1
    print("VERIFIED exact packet:",n,"files. Artifact integrity only."); return 0
if __name__=="__main__": sys.exit(main())
