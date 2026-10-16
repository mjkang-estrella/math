#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Independent parent authentication and guarded replay; integrity only."""
import ast, hashlib, json, pathlib, subprocess, sys
PROJECT = pathlib.Path(__file__).resolve().parents[4]
CAND = PROJECT / "frontier/campaigns/2026-10-14/nodal-power-four-review-r1"
ANCHOR = "5fcea71d539dbed6a5dd4c945b921b29acaf2aeb367932f5b654c96757193cdc"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(CAND/"seal.json") == ANCHOR
seal=json.loads((CAND/"seal.json").read_text())
e=seal["manifest"]
assert e["path"]=="manifest.json"
assert sha(CAND/e["path"])==e["sha256"] and (CAND/e["path"]).stat().st_size==e["size"]
m=json.loads((CAND/"manifest.json").read_text())
expected={"manifest.json","seal.json"}
for e in m["files"]:
    rel=pathlib.PurePosixPath(e["path"])
    assert not rel.is_absolute() and ".." not in rel.parts and str(rel)==e["path"] and str(rel) not in ("",".")
    assert str(rel) not in expected
    expected.add(str(rel))
    p=CAND/rel
    assert not p.is_symlink() and p.is_file()
    assert p.stat().st_size==e["size"] and sha(p)==e["sha256"]
files=set(); dirs={"."}
for p in CAND.rglob("*"):
    assert not p.is_symlink()
    if p.is_file(): files.add(p.relative_to(CAND).as_posix())
    elif p.is_dir(): dirs.add(p.relative_to(CAND).as_posix())
    else: raise AssertionError(p)
assert files==expected
assert dirs=={str(q) for p in expected for q in pathlib.PurePosixPath(p).parents}
fixed=[e for e in json.loads((CAND/"fixed-inputs-before.json").read_text())["files"] if e["role"]=="fixed-input"]
assert len(fixed)==61
for e in fixed:
    p=PROJECT/e["path"]
    assert p.stat().st_size==e["size"] and sha(p)==e["sha256"],p
protected=[CAND/p for p in expected]+[PROJECT/e["path"] for e in fixed]+[PROJECT/"frontier/NEW-TEN-2026-10-14.md"]
assert len(protected)==len(set(protected))
before={str(p):sha(p) for p in protected}
tree=json.loads((PROJECT/"sources/preprints-tree.json").read_text())
assert tree["truncated"] is False
idx={e["path"]:e for e in tree["tree"] if e["type"]=="blob"}
aroot=CAND/"inputs/author"
pins=json.loads((aroot/"git-identities.json").read_text())["files"]
for e in pins:
    data=(aroot/e["local"]).read_bytes()
    assert hashlib.sha1(b"blob %d\0"%len(data)+data).hexdigest()==e["git_blob_sha1"]==idx[e["upstream_path"]]["sha"]
guardtree=ast.parse((PROJECT/"frontier/campaigns/2026-10-14/nodal-power-four-parent/verify_frozen_r13.py").read_text())
guard=next(ast.literal_eval(n.value) for n in guardtree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="guard" for t in n.targets))
guard=guard.replace('sys.argv = [str(p), "--anchor=" + sys.argv[3]]',
    'sys.argv = [str(p), "--anchor=" + sys.argv[3], "--original-author", sys.argv[4]]')
runs=[]
for name,anchor,code in [("positive",ANCHOR,0),("wrong-anchor","0"*64,1)]:
    p=CAND/"verify.py"
    r=subprocess.run([sys.executable,"-B","-c",guard,str(p),sha(p),anchor,
        str(PROJECT/"frontier/campaigns/2026-10-14/fresh-analytic-discovery-r13")],capture_output=True,text=True)
    assert r.returncode==code,(name,r.stderr)
    runs.append(dict(name=name,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
assert before=={str(p):sha(p) for p in protected}
print(json.dumps(dict(anchor=ANCHOR,independent_manifest_and_exact_directory_authentication=True,
owned_files=len(expected),owned_directories_including_root=len(dirs),fixed_external_files=len(fixed),
mutable_ledger_observed_only=1,protected_files=len(protected),pinned_blobs=len(pins),
all_unchanged_during_verification=True,runs=runs,
limits="Integrity only. Reviewer mathematics verdict uses explicit repairs; unchanged author proof still needs revision. Contribution TECHNICAL, not campaign acceptance. Live ledger observed only during parent replay."),indent=2))
