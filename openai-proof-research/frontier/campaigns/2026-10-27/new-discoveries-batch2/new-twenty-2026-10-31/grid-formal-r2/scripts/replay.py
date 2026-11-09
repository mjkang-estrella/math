import os,sys,subprocess,hashlib,json,uuid,zipfile
from pathlib import Path
lane=Path(__file__).resolve().parent.parent
os.chdir(lane)
frozen=json.loads((lane/"frozen-before.json").read_text())
assert all(hashlib.sha256((lane/"src"/n).read_bytes()).hexdigest()==h for n,h in frozen.items())
pkg=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages")
build=lane/"build";build.mkdir(exist_ok=True)
(lane/"tmp").mkdir(exist_ok=True);(lane/"logs").mkdir(exist_ok=True)
runid=uuid.uuid4().hex[:12]
stampfile=lane/"replay-state.json"
state=json.loads(stampfile.read_text()) if stampfile.exists() else {}
def save(): stampfile.write_text(json.dumps(state,indent=2))
def run(name,args,checker=False,expected=0):
 env=os.environ.copy()
 if checker: env.update(LEAN_TOOL="leanchecker",LEAN_FLAGS="-j1 -M3500")
 path=lane/"logs"/(runid+"-"+name+".log")
 with path.open("w") as f:
  rc=subprocess.run([str(lane/"scripts/lean.sh")]+args,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 print(name,rc,path.name,flush=True)
 if (expected==0 and rc!=0) or (expected!=0 and rc==0):
  print(path.read_text()[-6000:]);raise SystemExit(1)
 return str(path.relative_to(lane))
# Read-only symlink overlay. Only the missing Attribute module is recompiled locally.
for base in pkg.glob("*/.lake/build/lib/lean"):
 for f in base.rglob("*"):
  if f.is_file():
   dest=build/f.relative_to(base)
   if not dest.exists():
    dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f)
attr=build/"Mathlib/Tactic/Bound/Attribute.olean"
if not attr.exists() or attr.is_symlink() or not attr.with_suffix(".olean.private").exists():
 for old in attr.parent.glob(attr.name+"*"):
  if old.is_symlink():old.unlink()
 run("cache-Attribute",["--root="+str(pkg/"mathlib"),"-o",str(attr),
     str(pkg/"mathlib/Mathlib/Tactic/Bound/Attribute.lean")])
mods=["GridBasic","GridSymmetry","GridFinal","GridChecks","GridRegression","Audit","GridPropagation","GridNeighbours","GridLattice","GridDeterminism","GridTransport","GridFinal2","Audit2"]
sourcehash=hashlib.sha256(b"".join((lane/"src"/(m+".lean")).read_bytes() for m in mods)).hexdigest()
if state.get("sourcehash")!=sourcehash: state={"sourcehash":sourcehash}
for m in mods:
 if not state.get(m) or not (build/(m+".olean")).exists():
  state[m]=run("compile-"+m,["--root=src","-o",str(build/(m+".olean")),"src/"+m+".lean"]);save()
 if not state.get("checker-"+m):
  state["checker-"+m]=run("checker-"+m,[m],checker=True);save()
for f in sorted((lane/"controls").glob("*.lean")):
 state[f.stem]=run("negative-"+f.stem,[str(f)],expected=1);save()
rows=[json.loads(s) for s in (lane/"audit.jsonl").read_text().splitlines()]
local=[r for r in rows if r["local"]]
upstream=[r for r in rows if not r["local"]]
def summary(rs):
 return {"declarations":len(rs),**{flag:sum(bool(r[flag]) for r in rs)
  for flag in ["unsafe","partial","axiom","unsafe_rec","implemented_by","extern"]},
  "transitive_axioms":sorted({a for r in rs for a in r["axioms"]})}
report={"status":"PARTIAL_CONDITIONAL","unconditional_endpoint":False,
 "lean_version":"4.34.1", "mathlib_revision":"d13f23b723b8a846827a245b89c10fc7d3f11612",
 "frozen_hashes_equal":True, "module_hashes":{m:hashlib.sha256((lane/"src"/(m+".lean")).read_bytes()).hexdigest() for m in mods},"LOCAL":summary(local),"upstream":summary(upstream),
 "endpoint_axioms":next(r["axioms"] for r in rows if r["name"]=="GridFinal2.mathdb_343536"),
 "inventory_equals_audited":"checked in Audit2.lean against every moduleData.constNames",
 "allowOpaque":True,
 "endpoint_import_closure":summary([r for r in rows if r["endpoint_import_closure"]]),
 "endpoint_import_closure_inventory_equals_audited":True,"state":state}
(lane/"replay-report.json").write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k!="state"},indent=2))
