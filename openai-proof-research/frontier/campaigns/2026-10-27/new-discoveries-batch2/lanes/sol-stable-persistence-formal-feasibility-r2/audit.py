import pathlib,hashlib,json,shutil,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
M=B.parents[1]/'2026-10-14/formal/.lake/packages/mathlib'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
if __name__=='__main__':
 (L/'frozen').mkdir(exist_ok=True); (L/'administrative').mkdir(exist_ok=True)
 records=[]
 for rel in ['sol-stable-persistence-breadth-depth-r225/PROOF.md','sol-stable-persistence-breadth-depth-r225/FAILURES.md','sol-stable-persistence-breadth-depth-r225/bindings.json','sol-stable-persistence-breadth-depth-r225/primarybytes.json','sol-stable-persistence-breadth-depth-r225/chronology.json','sol-stable-persistence-preliminary-review-r1/review.md','sol-stable-persistence-preliminary-review-r1/FAILURES.md','sol-stable-persistence-preliminary-review-r1/primary-coverage.json']:
  p=L.parent/rel; q=L/'frozen'/rel.replace('/','__'); h=sha(p); shutil.copyfile(p,q); assert sha(p)==h==sha(q); records.append({'original':str(p),'copy':str(q),'sha256':h})
 for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',B.parents[2]/'AGENTS.md']:
  if p.exists():
   q=L/'administrative'/p.name; shutil.copyfile(p,q)
 dump('bindings.json',records)
 head=(M/'.git/HEAD').read_text().strip(); assert head=='d13f23b723b8a846827a245b89c10fc7d3f11612',head
 files=sorted((M/'Mathlib').rglob('*.lean'))
 dump('mathlib-before.json',{'root':str(M),'head':head,'files':{str(p.relative_to(M)):sha(p) for p in files},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 print('Frozen inputs',len(records),'mathlib hashed',len(files),str(M))
