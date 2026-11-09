from pathlib import Path
import json,subprocess,hashlib
def write(n,t): subprocess.run(["python3","-I","-B","write_lane.py",n],input=t,text=True,check=True)
Path("replay/build").mkdir(parents=True,exist_ok=True)
assert not list(Path("replay/build").iterdir())
mods=json.loads(Path("SOURCE-ORDER.json").read_text())
for m in mods: write("replay/src/"+m+".lean",Path("src",m+".lean").read_text())
write("results/replay-plan.json",json.dumps({"modules":mods,"initial_build":[],"only_sources_extracted":True}))
metadata={}
counts=[]
receipts=[(p,json.loads(p.read_text())) for p in Path("receipt").iterdir() if p.suffix==".json"]
for k in range(8):
 ps=[(p,r) for p,r in receipts if r["label"]=="lean_ReviewOrigins"+str(k) and r["exit"]==0]
 assert len(ps)==1
 p,r=ps[0]
 a=[]
 for line in Path(r["log"]).open():
  if line.startswith("ENV_METADATA "): a=json.loads(line[13:])
 assert a
 counts.append(len(a))
 for d in a:
  assert d["name"] not in metadata
  metadata[d["name"]]=d
nodes=json.loads(Path("audit/own-nodes.json").read_text()); report=json.loads(Path("audit/own-closures.json").read_text())
production=set(mods)
actual={n for n,d in metadata.items() if d["origin"] in production}
assert actual==set(report["roots"])
for n,d in nodes.items():
 assert metadata[n]["origin"]==d["origin"] and metadata[n]["unsafe"]==d["unsafe"]
write("audit/environment-origins.json",json.dumps(metadata,sort_keys=True))
write("audit/origin-validation.json",json.dumps({"partition":"Lean Name.hash mod8","counts":counts,"whole_environment_count":len(metadata),"production_roots_exact":len(actual),"all_reachable_origins_match":True}))
print("METADATA VALIDATED",len(metadata),counts,"production",len(actual))
print("REPLAY SOURCES EXTRACTED",len(mods),"build initially empty")

