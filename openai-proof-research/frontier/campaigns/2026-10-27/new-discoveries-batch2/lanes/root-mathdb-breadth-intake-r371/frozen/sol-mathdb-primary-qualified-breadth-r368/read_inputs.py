from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):assert h(p)==e['sha256'] and p.stat().st_size==e.get('size',e.get('bytes')),str(p)
for e in json.loads((R/'bindings.json').read_text())['files']:check(Path(e['path']),e)
for n in ['root-mathdb-breadth-intake-r367','pi-mathdb-full-corpus-inventory-r301']:
 d=L/n;m=json.loads((d/'manifest.json').read_text())
 for e in m['files']:check(d/e['path'],e)
 print('MANIFEST PASS',n,len(m['files']))
a=json.loads((L/'root-mathdb-breadth-intake-r367/reserved-ids.json').read_text())['ids'];a=list(map(str,a))
b=list(map(str,json.loads((L/'root-mathdb-gram-intake-r359/reserved-ids.json').read_text())['ids']))
c=list(map(str,json.loads((L/'root-mathdb-breadth-intake-r365/reserved-ids.json').read_text())['ids']))
assert len(a)==len(set(a))==50 and not set(a)&set(b+c) and not set(b)&set(c)
q=json.loads((L/'root-mathdb-breadth-intake-r367/queue.json').read_text());assert set(a)=={str(x['mathdb_id']) for x in q}
print('SETS PASS 50 + 50 + 50 pairwise disjoint')
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 x=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,json.dumps(x)[:16000])
print('CAYLEY EXCLUSION', (L/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
print('LEDGER', (L.parent/'ledger.json').read_text()[:3000]);print('PRIOR CONTEXT',(L.parent/'prior-campaign-context.json').read_text()[:3000])
found=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').iterdir()):
 for i,line in enumerate(p.open(),1):
  x=json.loads(line)
  if str(x['mathdb_id']) in a:
   found.append(x)
   print('RECORD',json.dumps(x,ensure_ascii=False))
assert len(found)==50
(R/'records.json').write_text(json.dumps(found,indent=2,ensure_ascii=False)+'\n')
