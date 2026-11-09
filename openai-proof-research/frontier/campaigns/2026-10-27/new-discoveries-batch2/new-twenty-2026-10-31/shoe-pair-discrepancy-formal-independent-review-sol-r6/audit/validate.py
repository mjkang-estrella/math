import json, hashlib, subprocess
from pathlib import Path
rec=json.loads(Path("receipt/1794123894993604931_lean_ShoeReachableAudit.json").read_text())
assert rec["exit"]==0 and not rec["group_members_left"]
nodes={}; roots=[]; endpoints=[]; complete=None
for line in Path(rec["log"]).open():
 if line.startswith("AUDIT_ROOTS "): roots=json.loads(line[12:])
 elif line.startswith("AUDIT_ENDPOINTS "): endpoints=json.loads(line[16:])
 elif line.startswith("AUDIT_NODE "):
  d=json.loads(line[11:]); n=d["name"]; assert n not in nodes; nodes[n]=d
 elif line.startswith("AUDIT_COMPLETE "): complete=int(line.split()[1])
assert complete==len(nodes)
for n,d in nodes.items():
 assert all(v in nodes for v in d["typeDependencies"]+d["bodyDependencies"])
def closure(rs):
 seen=set(); pending=list(rs)
 while pending:
  n=pending.pop()
  if n in seen: continue
  seen.add(n); d=nodes[n]; pending.extend(d["typeDependencies"]); pending.extend(d["bodyDependencies"])
 return sorted(seen)
assert set(closure(roots))==set(nodes)
endpoints+=["Shoe.finite_zeroExtension_discrepancy","Shoe.finite_zeroExtension_outside","Shoe.colorConditionalMeasure_probability","Shoe.colorWinner_probability","Shoe.color_fallback_ae","Shoe.colorDiscrepancy_coding"]
closures={}
for n in endpoints:
 c=closure([n]); closures[n]={"closure":c,"count":len(c),"axioms":[x for x in c if nodes[x]["isAxiom"]],"unsafe":[x for x in c if nodes[x]["unsafe"]]}
allowed={"propext","Classical.choice","Quot.sound"}
ax=[n for n,d in nodes.items() if d["isAxiom"]]
assert set(ax)<=allowed
assert not any(d["unsafe"] for d in nodes.values())
controls={"ShoeControls","ShoeSemanticControls","ShoeColorControls"}
named={"ShoeAxiomAudit","ShoeEndpointAxioms"}
classes={n:("control" if nodes[n]["origin"] in controls else "named-audit" if nodes[n]["origin"] in named else "core") for n in roots}
report={"complete":True,"root_count":len(roots),"node_count":len(nodes),"roots":roots,"root_classes":classes,"closures":closures,"axioms":ax,"unsafe":[],"receipt":"receipt/1794123894993604931_lean_ShoeReachableAudit.json","log_sha256":rec["log_sha256"]}
def write(n,t): subprocess.run(["python3","-I","-B","write_lane.py",n],input=t,text=True,check=True)
write("audit/own-nodes.json",json.dumps(nodes,sort_keys=True))
write("audit/own-closures.json",json.dumps(report,sort_keys=True))
print("AUDIT SUMMARY",len(roots),len(nodes),"axioms",ax)
print("CLASS COUNTS",{c:list(classes.values()).count(c) for c in set(classes.values())})
print("CLOSURES",{n:{k:v for k,v in d.items() if k!="closure"} for n,d in closures.items()})
print("AUDIT LOG BYTES",Path(rec["log"]).stat().st_size)
print("BUILD HASHES")
out={}
for m in json.loads(Path("SOURCE-ORDER.json").read_text()):
 out[m]={n:hashlib.sha256(Path(p).read_bytes()).hexdigest() for n,p in [("source","src/"+m+".lean"),("olean","build/"+m+".olean")]}
write("results/build-hashes.json",json.dumps(out,sort_keys=True))

