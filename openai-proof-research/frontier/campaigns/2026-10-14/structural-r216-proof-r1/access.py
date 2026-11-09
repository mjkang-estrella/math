from pathlib import Path
import json,hashlib,sys,fnmatch,time
sys.dont_write_bytecode=True
ROOT=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OWN=ROOT/"frontier/campaigns/2026-10-14/structural-r216-proof-r1"
G=json.loads((OWN/"guards.json").read_text())
A=G["author_root"]
EXACT=set(G["direct"]+[A+"/packet/"+x for x in G["author_selected"]]+[A+"/"+x for x in G["author_outside"]])
def admit(p):
 p=Path(p); p=p if p.is_absolute() else ROOT/p
 rel=p.relative_to(ROOT).as_posix(); low=rel.casefold()
 if rel in EXACT or p.is_relative_to(OWN): return p
 if any(fnmatch.fnmatchcase(low,x) for x in G["wildcards"]+G["derivative_patterns"]) or any(x in low for x in G["substrings"]): raise PermissionError(rel)
 raise PermissionError("No exact admission: "+rel)
def log(d):
 with (OWN/"reads.jsonl").open("a") as f: f.write(json.dumps(d)+"\n")
def read(p,start=0,end=None,label="semantic"):
 p=admit(p); b=p.read_bytes(); end=len(b) if end is None else end
 assert 0<=start<=end<=len(b)
 data=b[start:end]
 log({"path":str(p.relative_to(ROOT)),"bytes":[start,end],"total":len(b),"sha256":hashlib.sha256(b).hexdigest(),"kind":label})
 return data
if __name__=="__main__":
 p=sys.argv[1]; start=int(sys.argv[2]) if len(sys.argv)>2 else 0; end=int(sys.argv[3]) if len(sys.argv)>3 else None
 print(read(p,start,end).decode())
