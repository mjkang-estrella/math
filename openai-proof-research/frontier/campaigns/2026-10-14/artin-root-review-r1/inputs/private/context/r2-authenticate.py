#!/usr/bin/env python3
"""Read-only parent authentication with one explicit historical-context substitution.
Original code MIT. Does not execute child code or issue a mathematical verdict.
"""
from pathlib import Path
import hashlib, json
BASE = Path(__file__).resolve().parent
C = BASE.parent
REPO = C.parents[2]
CONFIG = {
 "coulomb-positive-parent": ("coulomb-positive-r2", "6abfc33fde05431aaf609bce2e95554528f6050fe23aa5cfc496bd9810c4ba7b"),
 "artin-root-parent": ("artin-root-r2", "92f9d1b04e4631cb436a58b7aeb46c2444f25d63fff50522ea0a7cc155735003")
}
name, anchor = CONFIG[BASE.name]
root = C/name
def rec(p):
 b=p.read_bytes()
 return {"size":len(b),"sha256":hashlib.sha256(b).hexdigest()}
def check(p,e):
 assert p.is_file() and not p.is_symlink(), str(p)
 assert rec(p)=={k:e[k] for k in ("size","sha256")}, str(p)
def member(r):
 ans=set()
 for p in r.rglob("*"):
  assert not p.is_symlink(),str(p)
  if p.is_file():ans.add(p.relative_to(r).as_posix())
 return ans
def local(r,s):
 p=Path(s);assert not p.is_absolute() and ".." not in p.parts
 return r/p
assert rec(root/"seal.json")["sha256"]==anchor
seal=json.loads((root/"seal.json").read_text())
manifests=seal.get("manifests") or {seal[k]["path"]:seal[k] for k in ("inputs","outputs")}
expected={"seal.json","seal.sha256","inputs-manifest.json","outputs-manifest.json"}
for mn,e in manifests.items():
 check(local(root,mn),e)
 for row in json.loads((root/mn).read_text())["files"]:
  assert row["path"] not in expected
  check(local(root,row["path"]),row);expected.add(row["path"])
assert member(root)==expected
if name=="coulomb-positive-r2":
 b=json.loads((root/"external-input-baseline.json").read_text())
 files=b["files"]
 for g in b["exact_groups"]:assert member(REPO/g["root"])==set(g["members"])
else:
 b=json.loads((root/"external-inputs.json").read_text())
 files=b["files"]
 for g in b["trees"]:
  r=Path(g["root"])
  assert member(r)=={e["path"] for e in g["inventory"]}
  for row in g["inventory"]:check(local(r,row["path"]),row)
substitutions=0
for e in files:
 p=Path(e["path"])
 if not p.is_absolute():p=REPO/p
 if p==REPO/"frontier/NEW-TEN-2026-10-14.md":
  p=BASE/"r2-ledger-snapshot.md";substitutions+=1
 check(p,e)
assert substitutions==1
print(json.dumps({"status":"PASS_HASH_ONLY_WITH_DECLARED_HISTORICAL_LEDGER","package":name,
 "anchor":anchor,"own_files":len(expected),"external_manifest_records":len(files),
 "historical_ledger_substitutions":1,"child_code_executed":False,
 "mathematical_or_contribution_verdict":False,"writes":False},sort_keys=True))
