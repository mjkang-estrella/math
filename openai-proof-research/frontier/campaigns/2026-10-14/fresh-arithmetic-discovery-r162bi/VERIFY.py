#!/usr/bin/env python3
"""Read-only artifact verifier; explicit detached anchors required. No math gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

DETACHED = {"MANIFEST.json", "REPORT.md"}
PREFIX = "preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ORIGINALS = [
 "frontier/campaigns/2026-10-14/discovery-arithmetic-r162bh-parent/assessment.md",
 "frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bh/private/DERIVATIONS.md",
 "frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bh/private/WORKING.md",
 "frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bh/private/READING-LIMITS.md",
 "frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bh/FINAL.md",
]
PROJECT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")

def sha(data): return hashlib.sha256(data).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)
def safe(name):
    require(isinstance(name,str) and name and "\\" not in name, "unsafe path")
    p=PurePosixPath(name)
    require(not p.is_absolute() and all(x not in (".","..","") for x in name.split("/")) and p.as_posix()==name, "unsafe path")
    return name

def inventory(root):
    root=Path(root)
    require(stat.S_ISDIR(root.lstat().st_mode),"root is not a real directory")
    files={}; dirs={".":root.lstat().st_mode}
    for base, names, fnames in os.walk(root,followlinks=False):
        for n in sorted(names):
            p=Path(base)/n; mode=p.lstat().st_mode
            require(stat.S_ISDIR(mode),"non-directory/symlink in directory set")
            dirs[p.relative_to(root).as_posix()]=mode
        for n in sorted(fnames):
            p=Path(base)/n; mode=p.lstat().st_mode
            require(stat.S_ISREG(mode),"non-regular/symlink payload")
            files[p.relative_to(root).as_posix()]=mode
    return files,dirs

def record(root,name):
    safe(name); p=Path(root)/name; data=p.read_bytes()
    return dict(path=name,size=len(data),sha256=sha(data),mode=p.lstat().st_mode)

def make_manifest(root,kind):
    files,dirs=inventory(root)
    return dict(schema=1,kind=kind,files=[record(root,n) for n in sorted(set(files)-DETACHED)],
        directories=[dict(path=n,mode=dirs[n]) for n in sorted(dirs)],
        detached_modes={n:stat.S_IFREG|0o644 for n in sorted(DETACHED)})

def verify_payload(root,m,detached_present):
    require(m.get("schema")==1 and m.get("kind") in ("r162bi","tiny-control"),"bad schema/kind")
    require(set(detached_present)<=DETACHED,"bad detached set")
    rows=m["files"]; names=[safe(x["path"]) for x in rows]
    require(names==sorted(names) and len(names)==len(set(names)),"records not sorted unique")
    require(not (set(names)&DETACHED),"detached file included in payload")
    actual,dirs=inventory(root)
    require(set(actual)==set(names)|set(detached_present),"exact file membership mismatch")
    drows=m["directories"]; dn=[x["path"] for x in drows]
    require(dn==sorted(dn) and len(dn)==len(set(dn)),"directory records not sorted unique")
    for n in dn:
        if n!=".": safe(n)
    require(dirs=={x["path"]:x["mode"] for x in drows},"directory membership/mode mismatch")
    for item in rows:
        require(record(root,item["path"])==item,"payload bytes/length/mode mismatch: "+item["path"])
    require(set(m["detached_modes"])==DETACHED,"detached mode schema")
    for n in detached_present:
        require(actual[n]==m["detached_modes"][n],"detached mode mismatch")
    if m["kind"]=="r162bi": verify_bindings(root)
    return dict(payload_records=len(rows),payload_bytes=sum(x["size"] for x in rows),
        whole_files=len(actual),directories_including_root=len(dirs))

def verify_bindings(root):
    root=Path(root)
    tree=json.loads((root/"private/source-tree.json").read_text())
    require(len(tree)==16 and len({e["path"] for e in tree})==16,"source tree membership")
    by={e["path"]:e for e in tree}
    require(PREFIX in by and all(p==PREFIX or p.startswith(PREFIX+"/") for p in by),"source prefix")
    bs=json.loads((root/"private/source-bindings.json").read_text())
    require(len(bs)==12 and len({x["path"] for x in bs})==12,"source blob uniqueness")
    require({x["path"] for x in bs}=={e["path"] for e in tree if e["type"]=="blob"},"source blob membership")
    for b in bs:
        e=by[b["path"]]
        require(all(b[k]==e[k] for k in ("path","mode","type","sha","size")),"source metadata binding")
        require(b["url"]=="https://raw.githubusercontent.com/openai/math/"+PIN+"/"+b["path"],"source pin/url")
        expected="private/source/"+b["path"][len(PREFIX)+1:]
        require(b["local"]==expected,"source local mapping")
        data=(root/safe(expected)).read_bytes()
        require(len(data)==b["size"] and sha(data)==b["sha256"],"source bytes")
        blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        require(blob==b["sha"],"source Git blob mismatch")
    for e in tree:
        if e["type"]!="tree": continue
        children=[c for c in tree if str(PurePosixPath(c["path"]).parent)==e["path"]]
        children.sort(key=lambda c:(PurePosixPath(c["path"]).name+("/" if c["type"]=="tree" else "")).encode())
        data=b"".join(format(int(c["mode"],8),"o").encode()+b" "+PurePosixPath(c["path"]).name.encode()+b"\0"+bytes.fromhex(c["sha"]) for c in children)
        got=hashlib.sha1(b"tree "+str(len(data)).encode()+b"\0"+data).hexdigest()
        require(got==e["sha"],"source Git tree mismatch")
    completed=json.loads((root/"private/completed-bindings.json").read_text())
    require([x["original"] for x in completed]==ORIGINALS,"completed originals not exact authorized five")
    expected_copies=["private/completed/1-assessment.md","private/completed/2-DERIVATIONS.md","private/completed/3-WORKING.md","private/completed/4-READING-LIMITS.md","private/completed/5-FINAL.md"]
    require([x["copy"] for x in completed]==expected_copies,"completed copies mapping")
    for b in completed:
        for p in (PROJECT/b["original"],root/b["copy"]):
            require(p.lstat().st_mode==b["mode"] and stat.S_ISREG(b["mode"]),"completed original/copy full mode changed")
            data=p.read_bytes()
            require(len(data)==b["size"] and sha(data)==b["sha256"],"completed original/copy bytes changed")
    primary=json.loads((root/"private/primary/bindings.json").read_text())
    successes=[x for x in primary if "size" in x]
    require([x["name"] for x in successes]==["SS","AGS","BSTW","Meiburg","ABKM"],"primary success membership")
    for b in successes:
        data=(root/("private/primary/"+b["name"]+".pdf")).read_bytes()
        require(len(data)==b["size"] and sha(data)==b["sha256"],"primary PDF binding")
        require((root/("private/primary/"+b["name"]+".txt")).stat().st_size==b["text_bytes"],"primary extraction size")

def verify_anchored(root,final_anchor,manifest_anchor,report_anchor):
    root=Path(root)
    for n,h in [("FINAL.md",final_anchor),("MANIFEST.json",manifest_anchor),("REPORT.md",report_anchor)]:
        require(isinstance(h,str) and re.fullmatch(r"[0-9a-f]{64}",h),"invalid explicit anchor")
        require(sha((root/n).read_bytes())==h,"detached anchor mismatch: "+n)
    m=json.loads((root/"MANIFEST.json").read_text())
    return verify_payload(root,m,DETACHED)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("root"); p.add_argument("--final",required=True); p.add_argument("--manifest",required=True); p.add_argument("--report",required=True)
    a=p.parse_args()
    result=verify_anchored(a.root,a.final,a.manifest,a.report)
    print(json.dumps(dict(artifact_status="MATCH",**result),sort_keys=True))

if __name__=="__main__": main()
