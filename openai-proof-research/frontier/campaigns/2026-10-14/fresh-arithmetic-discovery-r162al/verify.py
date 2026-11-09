#!/usr/bin/env python3
"""Read-only exact-packet integrity verification; no mathematical verdict."""
import argparse, hashlib, json, os
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("root",type=Path)
    for name in ("final", "manifest", "report"):
        ap.add_argument("--"+name+"-sha256",required=True)
    a=ap.parse_args(); root=a.root.resolve()
    fixed={"final":"FINAL.md","manifest":"private/MANIFEST.json","report":"REPORT.md"}
    for name, rel in fixed.items():
        expected=getattr(a,name+"_sha256")
        if len(expected)!=64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("Invalid explicit anchor: "+name)
        p=root/rel
        if p.is_symlink() or digest(p)!=expected:
            raise ValueError("Detached anchor mismatch: "+name)
    m=json.loads((root/fixed["manifest"]).read_text())
    if m.get("format")!="r162al-exact-packet-v1": raise ValueError("Unknown manifest format")
    entries=m["files"]; seen=set()
    for e in entries:
        rel=e["path"]; q=Path(rel)
        if q.is_absolute() or ".." in q.parts or str(q)!=rel or rel in seen:
            raise ValueError("Unsafe or duplicate manifest path")
        seen.add(rel); p=root/q
        if any((root/Path(*q.parts[:i])).is_symlink() for i in range(1,len(q.parts)+1)):
            raise ValueError("Symlink in packet")
        if p.stat().st_size!=e["bytes"] or digest(p)!=e["sha256"]:
            raise ValueError("Payload mismatch: "+rel)
    actual=set()
    for base,dirs,files in os.walk(root,followlinks=False):
        for name in dirs+files:
            if (Path(base)/name).is_symlink(): raise ValueError("Symlink under root")
        relbase=Path(base).relative_to(root).as_posix()
        if relbase=="private/integrity-controls":
            dirs[:]=[]; continue
        for name in files:
            rel=(Path(base)/name).relative_to(root).as_posix()
            if rel not in ("private/MANIFEST.json","REPORT.md"):
                actual.add(rel)
    if actual!=seen: raise ValueError("Exact file-set mismatch")
    print(json.dumps({"integrity":"verified","files":len(entries),"mathematical_gate":False}))

if __name__=="__main__":
    main()
