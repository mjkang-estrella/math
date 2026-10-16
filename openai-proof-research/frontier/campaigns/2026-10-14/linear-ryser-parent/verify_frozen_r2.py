#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
import ast, hashlib, json, pathlib, subprocess, sys
PROJECT = pathlib.Path(__file__).resolve().parents[4]
CAND = PROJECT / "frontier/campaigns/2026-10-14/linear-ryser-r2"
ANCHOR = "06c49552725059e5522dd6e067ea5d26468339a44e4894e7a30f1f8e5af8c3e4"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert (CAND/"seal.json").stat().st_size == 406 and sha(CAND/"seal.json") == ANCHOR
seal=json.loads((CAND/"seal.json").read_text())
assert sha(CAND/"manifest.json") == seal["manifest_sha256"]
assert (CAND/"manifest.json").stat().st_size == seal["manifest_size"]
m=json.loads((CAND/"manifest.json").read_text())
expected=set(m["metadata"])
assert expected == {"manifest.json","seal.json"}
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
assert files==expected and dirs==set(m["directories"])
history=json.loads((CAND/"unchanged-source-receipts.json").read_text())
fixed=[dict(path=e["path"], **e["before"]) for e in history["fixed_files"]]
assert len(fixed)==history["fixed_count"]==46
assert all(e["before"]==e["after"] and e["unchanged"] for e in history["fixed_files"])
for e in fixed:
    p=PROJECT/e["path"]
    assert p.stat().st_size==e["size"] and sha(p)==e["sha256"],p
protected=[CAND/p for p in expected]+[PROJECT/e["path"] for e in fixed]+[PROJECT/"frontier/NEW-TEN-2026-10-14.md"]
assert len(protected)==len(set(protected))
before={str(p):sha(p) for p in protected}
tree=json.loads((PROJECT/"sources/preprints-tree.json").read_text())
assert tree["truncated"] is False
idx={e["path"]:e for e in tree["tree"] if e["type"]=="blob"}
pins=json.loads((CAND/"inputs/pinned-records.json").read_text())
for e in pins:
    data=(CAND/e["local"]).read_bytes()
    assert hashlib.sha1(b"blob %d\0"%len(data)+data).hexdigest()==e["git_blob"]==idx[e["path"]]["sha"]
# Reuse the already inspected read-only execution guard, without executing its parent module.
guardtree=ast.parse((PROJECT/"frontier/campaigns/2026-10-14/nodal-power-four-parent/verify_frozen_r13.py").read_text())
guard=next(ast.literal_eval(n.value) for n in guardtree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="guard" for t in n.targets))
guard=guard.replace('"--anchor=" + sys.argv[3]','"--seal-sha256=" + sys.argv[3]')
runs=[]
for name,anchor,code in [("positive",ANCHOR,0),("wrong-anchor","0"*64,1)]:
    p=CAND/"verify.py"
    r=subprocess.run([sys.executable,"-B","-c",guard,str(p),sha(p),anchor],capture_output=True,text=True)
    assert r.returncode==code,(name,r.stderr)
    runs.append(dict(name=name,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
p=CAND/"diagnostics/check_k4.py"
assert sha(p)=="dbc0955622f197645b89f1acb45002fcd724e047d1d16de6ef0ed4198a33358e"
r=subprocess.run([sys.executable,"-B","-c",guard,str(p),sha(p),ANCHOR],capture_output=True,text=True)
assert r.returncode==0,r.stderr
assert json.loads(r.stdout)==json.loads((CAND/"diagnostics/k4-result.json").read_text())
assert before=={str(p):sha(p) for p in protected}
print(json.dumps(dict(anchor=ANCHOR,independent_manifest_and_exact_directory_authentication=True,
owned_files=len(expected),owned_directories_including_root=len(dirs),fixed_external_files=len(fixed),
mutable_ledger_observed_only=1,protected_files=len(protected),pinned_blobs=len(pins),
all_unchanged_during_verification=True,runs=runs,diagnostic=dict(exit_code=r.returncode,recorded_result_exact_match=True,
scope="15 joins and 12 singleton old labels over F4 only; not full LR, classification, or all-field extension proof"),
limits="Integrity and one finite incidence diagnostic only; no full-target mathematical acceptance."),indent=2))
