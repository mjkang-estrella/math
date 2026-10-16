#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
import ast, hashlib, json, pathlib, subprocess, sys
PROJECT=pathlib.Path(__file__).resolve().parents[4]
CAND=PROJECT/"frontier/campaigns/2026-10-14/fresh-structural-discovery-r16"
ANCHOR="fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(CAND/"seal.json")==ANCHOR and (CAND/"seal.json").stat().st_size==416
s=json.loads((CAND/"seal.json").read_text())
assert sha(CAND/"manifest.json")==s["manifest_sha256"] and (CAND/"manifest.json").stat().st_size==s["manifest_size"]
m=json.loads((CAND/"manifest.json").read_text()); expected={"manifest.json","seal.json"}
for e in m["files"]:
    r=pathlib.PurePosixPath(e["path"])
    assert str(r)==e["path"] and not r.is_absolute() and ".." not in r.parts and str(r) not in ("",".")
    assert str(r) not in expected
    expected.add(str(r)); p=CAND/r
    assert p.is_file() and not p.is_symlink() and p.stat().st_size==e["size"] and sha(p)==e["sha256"]
files=set(); dirs={"."}
for p in CAND.rglob("*"):
    assert not p.is_symlink()
    if p.is_file(): files.add(p.relative_to(CAND).as_posix())
    elif p.is_dir(): dirs.add(p.relative_to(CAND).as_posix())
    else: raise AssertionError(p)
assert files==expected and dirs==set(m["directories"])
fixed=json.loads((CAND/"unchanged-source-receipts.json").read_text())["fixed_files"]
for e in fixed:
    assert sha(PROJECT/e["path"])==e["before"]["sha256"]==e["after"]["sha256"]
brief=PROJECT/"frontier/campaigns/2026-10-14/linear-ryser-parent/fresh-r16-brief.txt"
protected=[CAND/p for p in expected]+[PROJECT/e["path"] for e in fixed]+[brief,PROJECT/"frontier/NEW-TEN-2026-10-14.md",PROJECT/"frontier/campaigns/2026-10-14/tasks.json"]
assert len(protected)==len(set(protected))
before={str(p):sha(p) for p in protected}
tree=json.loads((PROJECT/"sources/preprints-tree.json").read_text())
assert tree["truncated"] is False
idx={e["path"]:e for e in tree["tree"] if e["type"]=="blob"}
pins=json.loads((CAND/"inputs/pinned-records.json").read_text())["pinned"]
for e in pins:
    data=(CAND/e["local"]).read_bytes()
    assert hashlib.sha1(b"blob %d\0"%len(data)+data).hexdigest()==e["git_blob_sha1"]==idx[e["upstream_path"]]["sha"]
guardtree=ast.parse((PROJECT/"frontier/campaigns/2026-10-14/nodal-power-four-parent/verify_frozen_r13.py").read_text())
guard=next(ast.literal_eval(n.value) for n in guardtree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="guard" for t in n.targets))
guard=guard.replace('"--anchor=" + sys.argv[3]','"--seal-sha256=" + sys.argv[3]')
runs=[]
for name,anchor,code in [("positive",ANCHOR,0),("wrong-anchor","0"*64,1)]:
    p=CAND/"verify.py"
    r=subprocess.run([sys.executable,"-B","-c",guard,str(p),sha(p),anchor],capture_output=True,text=True)
    assert r.returncode==code,(name,r.stderr)
    runs.append(dict(name=name,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
assert before=={str(p):sha(p) for p in protected}
print(json.dumps(dict(anchor=ANCHOR,independent_manifest_and_exact_directory_authentication=True,
owned_files=len(expected),owned_directories_including_root=len(dirs),fixed_source_external_files=len(fixed),
fixed_original_brief=1,original_brief_sha256=sha(brief),mutable_ledger_and_tasks_observed_only=2,
protected_files=len(protected),pinned_blobs=len(pins),all_unchanged_during_verification=True,runs=runs,
limits="Integrity only. No numerical diagnostic rerun or mathematical acceptance. Child brief snapshot is a transcription, not asserted byte-identical to original parent brief."),indent=2))
