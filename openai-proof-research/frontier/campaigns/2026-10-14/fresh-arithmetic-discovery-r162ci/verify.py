#!/usr/bin/env python3
"""Read-only artifact verifier. Supply all three detached anchors externally."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
PREFIXES = ["preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026", "preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026"]
ORIGINALS = ["frontier/campaigns/2026-10-14/discovery-arithmetic-r162ch-parent/assessment.md"] + ["frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ch/" + x for x in ["private/DERIVATION.md", "private/WORKING.md", "private/READING-LIMITS.md", "FINAL.md"]]
def require(ok, message):
    if not ok: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def safe(s):
    require(isinstance(s,str) and s and "\\" not in s, "unsafe path")
    p=PurePosixPath(s)
    require(not p.is_absolute() and all(x not in (".","..","") for x in p.parts) and p.as_posix()==s, "unsafe path")
    return s
def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink(), "unsafe root")
    files={}; dirs={}
    def walk(d):
        for e in os.scandir(d):
            p=Path(e.path); rel=p.relative_to(root).as_posix(); safe(rel); st=p.lstat()
            require(not stat.S_ISLNK(st.st_mode), "symlink: "+rel)
            if stat.S_ISDIR(st.st_mode): dirs[rel]=st.st_mode; walk(p)
            else:
                require(stat.S_ISREG(st.st_mode), "nonregular: "+rel)
                files[rel]=(st.st_mode,st.st_size)
    walk(root)
    return files,dirs
def verify(root, project, final_anchor, manifest_anchor, report_anchor):
    root=Path(root); project=Path(project)
    files,dirs=inventory(root)
    for name,anchor in [("FINAL.md",final_anchor),("MANIFEST.json",manifest_anchor),("REPORT.md",report_anchor)]:
        require(len(anchor)==64 and all(c in "0123456789abcdef" for c in anchor), "anchor format")
        require(name in files and sha((root/name).read_bytes())==anchor, "anchor mismatch: "+name)
    m=json.loads((root/"MANIFEST.json").read_bytes())
    require(m["format"] in ("r162ci-v1","r162ci-v1-fixture"), "format")
    require(root.stat().st_mode==m["root_mode"], "root mode")
    records=m["files"]; paths=[safe(x["path"]) for x in records]
    require(paths==sorted(paths) and len(paths)==len(set(paths)), "file order/uniqueness")
    require(set(files)==set(paths)|{"MANIFEST.json","REPORT.md"}, "exact file membership")
    drec=m["directories"]; dp=[safe(x["path"]) for x in drec]
    require(dp==sorted(dp) and len(dp)==len(set(dp)), "directory order/uniqueness")
    require(dirs=={x["path"]:x["mode"] for x in drec}, "exact directory membership/modes")
    for x in records:
        f=root/x["path"]; require(files[x["path"]]==(x["mode"],x["bytes"]), "mode/length: "+x["path"])
        require(sha(f.read_bytes())==x["sha256"], "hash: "+x["path"])
    for name in ["MANIFEST.json","REPORT.md"]:
        require(files[name][0]==m["detached_modes"][name], "detached mode: "+name)
    report=(root/"REPORT.md").read_text()
    require("FINAL SHA256 "+final_anchor in report and "MANIFEST SHA256 "+manifest_anchor in report, "report binding")
    if m["format"]=="r162ci-v1":
        require(m["pin"]==PIN, "pin")
        raw=(project/"sources/preprints-tree.json").read_bytes()
        require(len(raw)==4858136 and sha(raw)==TREE_SHA, "complete tree binding")
        tree=json.loads(raw); es=tree["tree"] if isinstance(tree,dict) else tree
        require(len(es)==13223, "complete tree entry count")
        sel=json.loads((root/"private/tree-selection.json").read_bytes())
        actual=[x for x in es if any(x["path"]==p or x["path"].startswith(p+"/") for p in PREFIXES)]
        require(sorted(sel,key=lambda x:x["path"])==sorted(actual,key=lambda x:x["path"]), "exact source selection")
        require(len(sel)==34, "selection size")
        by={x["path"]:x for x in sel}
        bindings=json.loads((root/"private/source-bindings.json").read_bytes())
        require(len(bindings)==28 and len({x["upstream"] for x in bindings})==28, "blob uniqueness")
        for x in bindings:
            require(x["upstream"] in by and by[x["upstream"]]["type"]=="blob", "blob member")
            require(x["path"]=="private/source/"+x["upstream"], "source path")
            require(x["url"]=="https://raw.githubusercontent.com/openai/math/"+PIN+"/"+x["upstream"], "pinned URL")
            data=(root/safe(x["path"])).read_bytes()
            blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
            require(blob==x["git_blob"]==by[x["upstream"]]["sha"] and len(data)==x["bytes"]==by[x["upstream"]]["size"] and sha(data)==x["sha256"], "blob binding")
        for x in sel:
            if x["type"]!="tree": continue
            cs=[c for c in sel if str(PurePosixPath(c["path"]).parent)==x["path"]]
            cs.sort(key=lambda c:(PurePosixPath(c["path"]).name+("/" if c["type"]=="tree" else "")).encode())
            body=b"".join((c["mode"].lstrip("0")+" "+PurePosixPath(c["path"]).name).encode()+b"\0"+bytes.fromhex(c["sha"]) for c in cs)
            require(hashlib.sha1(b"tree "+str(len(body)).encode()+b"\0"+body).hexdigest()==x["sha"], "Git tree binding")
        copies=json.loads((root/"private/completed-bindings.json").read_bytes())
        require([x["original"] for x in copies]==ORIGINALS, "exact completed exceptions")
        for x in copies:
            for f in [project/x["original"],root/safe(x["copy"])]:
                st=f.lstat(); require(stat.S_ISREG(st.st_mode) and st.st_mode==x["mode"] and st.st_size==x["bytes"] and sha(f.read_bytes())==x["sha256"], "completed original/copy binding")
        prim=json.loads((root/"private/primary/bindings.json").read_bytes())
        require(len(prim)==8, "primary count")
        for x in prim:
            for ext in ["pdf","txt"]:
                f=root/safe(x[ext+"_path"]); data=f.read_bytes()
                require(f.stat().st_mode==x[ext+"_mode"] and sha(data)==x[ext+"_sha256"], "primary binding")
                require(len(data)==x["bytes" if ext=="pdf" else "text_bytes"], "primary length")
    return {"status":"MATCH", "payload_files":len(records), "whole_root_files":len(files), "directories_including_root":len(dirs)+1, "payload_bytes":sum(x["bytes"] for x in records)}
def main():
    a=argparse.ArgumentParser();a.add_argument("--root",required=True);a.add_argument("--project-root",required=True)
    for s in ["final","manifest","report"]:a.add_argument("--"+s+"-sha256",required=True)
    x=a.parse_args();print(json.dumps(verify(x.root,x.project_root,x.final_sha256,x.manifest_sha256,x.report_sha256),sort_keys=True))
if __name__=="__main__": main()
