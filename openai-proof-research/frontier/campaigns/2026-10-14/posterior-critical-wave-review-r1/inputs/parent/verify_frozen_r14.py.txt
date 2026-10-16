#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only parent authentication/replay; no mathematics certification."""
import ast, hashlib, json, pathlib, subprocess, sys
PROJECT=pathlib.Path(__file__).resolve().parents[4]
CAND=PROJECT/"frontier/campaigns/2026-10-14/fresh-analytic-discovery-r14"
ANCHOR="49b43b219fe230515189cc76f3170ecb5334f21dbb971ebf71b9aee2f3c3c9b4"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(CAND/"seal.json")==ANCHOR
s=json.loads((CAND/"seal.json").read_text()); e=s["manifest"]
assert e["path"]=="manifest.json" and sha(CAND/e["path"])==e["sha256"] and (CAND/e["path"]).stat().st_size==e["size"]
m=json.loads((CAND/"manifest.json").read_text()); expected={"manifest.json","seal.json"}
for e in m["files"]:
    r=pathlib.PurePosixPath(e["path"])
    assert str(r)==e["path"] and not r.is_absolute() and ".." not in r.parts and str(r) not in ("",".")
    assert str(r) not in expected
    expected.add(str(r)); p=CAND/r
    assert p.is_file() and not p.is_symlink() and p.stat().st_size==e["size"] and sha(p)==e["sha256"]
files=set(); dirs=set()
for p in CAND.rglob("*"):
    assert not p.is_symlink()
    if p.is_file(): files.add(p.relative_to(CAND).as_posix())
    elif p.is_dir(): dirs.add(p.relative_to(CAND).as_posix())
    else: raise AssertionError(p)
assert files==expected and dirs==set(m["directories"])
external=json.loads((CAND/"inputs/unchanged-inputs.json").read_text())["context"]
fixed=[e for e in external if e["role"]!="mutable-context"]
for e in fixed:
    assert sha(PROJECT/e["external_path"])==e["before_sha256"]==e["after_observed_sha256"]
protected=[CAND/p for p in expected]+[PROJECT/e["external_path"] for e in external]
assert len(protected)==len(set(protected))
before={str(p):sha(p) for p in protected}
tree=json.loads((PROJECT/"sources/preprints-tree.json").read_text())
assert tree["truncated"] is False
idx={e["path"]:e for e in tree["tree"] if e["type"]=="blob"}
pins=json.loads((CAND/"inputs/source-authentication.json").read_text())["records"]
for e in pins:
    data=(CAND/e["path"]).read_bytes()
    assert hashlib.sha1(b"blob %d\0"%len(data)+data).hexdigest()==e["git_blob"]==idx[e["upstream_path"]]["sha"]
guardtree=ast.parse((PROJECT/"frontier/campaigns/2026-10-14/nodal-power-four-parent/verify_frozen_r13.py").read_text())
guard=next(ast.literal_eval(n.value) for n in guardtree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="guard" for t in n.targets))
guard=guard.replace('sys.argv = [str(p), "--anchor=" + sys.argv[3]]','sys.argv = [str(p), "--anchor=" + sys.argv[3], "--controls"]')
runs=[]
for name,anchor,code in [("positive-with-controls",ANCHOR,0),("wrong-anchor","0"*64,1)]:
    p=CAND/"verify.py"
    assert sha(p)=="535f514b4764e649eb382fc61d4dc498ba94f2943426d1d08370564f3a68dbb2"
    r=subprocess.run([sys.executable,"-B","-c",guard,str(p),sha(p),anchor],capture_output=True,text=True)
    assert r.returncode==code,(name,r.stderr)
    runs.append(dict(name=name,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
assert before=={str(p):sha(p) for p in protected}
print(json.dumps(dict(anchor=ANCHOR,independent_manifest_and_exact_directory_authentication=True,
owned_files=len(expected),owned_directories_excluding_root=len(dirs),fixed_external_files=len(fixed),
mutable_ledger_observed_only=1,protected_files=len(protected),pinned_blobs=len(pins),
all_unchanged_during_verification=True,runs=runs,limits="Integrity only; no mathematical experiment or proof acceptance."),indent=2))
