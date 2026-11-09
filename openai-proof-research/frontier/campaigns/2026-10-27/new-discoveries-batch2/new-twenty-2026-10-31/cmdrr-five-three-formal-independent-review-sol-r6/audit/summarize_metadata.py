import json,pathlib,collections,subprocess,sys,hashlib
p=pathlib.Path.cwd()
r=json.loads((p/'receipt/1794124527902576453_metadata_compile_v1.json').read_text())
print("receipt keys",list(r))
log=(p/'logs/1794124527902576453_metadata_compile_v1.log').read_text()
nodes=[json.loads(x.split("NODE ",1)[1]) for x in log.splitlines() if x.startswith("NODE ")]
roots=json.loads(next(x[6:] for x in log.splitlines() if x.startswith("ROOTS ")))
out={"roots":roots,"nodes":nodes}
text=json.dumps(out,indent=2)
subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),"audit/METADATA.json"],input=text,text=True,check=True)
for scope in ["production","auxiliary"]:
 ns=[n for n in nodes if n["scope"]==scope]
 print(scope,len(ns),"roots",len(roots[scope]),"kinds",dict(collections.Counter(n["kind"] for n in ns)))
 print("axioms",[n["name"] for n in ns if n["kind"]=="axiom"])
 print("unsafe/partial",[(n["name"],n["unsafe"],n["partial"]) for n in ns if n["unsafe"] or n["partial"]])
 print("runtime",[(n["name"],n["extern"],n["implementedBy"],n["csimp"]) for n in ns if n["extern"] or n["implementedBy"] or n["csimp"]])
print("pin/source/context",[(f,len((p/f).read_bytes())) for f in ["inputs/source/sources/design-final.txt","inputs/source/sources/design.txt"]])
print("final theorem lines")
for f in ["inputs/source/sources/design-final.txt","inputs/source/sources/design.txt"]:
 print(f)
 for i,l in enumerate((p/f).read_text().splitlines(),1):
  if any(w in l for w in ["Theorem","Conjecture","Lemma","Corollary","5, 3","5,3"]): print(i,l)

