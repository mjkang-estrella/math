import json,hashlib,gzip,re,time,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parent; R=L.parents[5]
(L/'sources').mkdir(exist_ok=True)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
frozen=[]
for p in [R/'AGENTS.md',B.parent/'AGENTS.md',B.parent/'ledger.json',B.parent/'NEXT.md',B.parent/'prior-campaign-context.json',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 frozen.append({'path':str(p),'sha256':digest(p)})
 if p.name=='ledger.json':
  d=json.loads(p.read_text());print('accepted titles',[x['title'] for x in d['accepted']]);print('other keys',list(d))
 if p.name=='prior-campaign-context.json':
  d=json.loads(p.read_text());print('prior titles',[x.get('title') for v in d.values() if isinstance(v,list) for x in v if isinstance(x,dict)])
 if p.name=='NEXT.md':
  with p.open() as f:
   for s in f:
    if re.search('matroid|Grothendieck|rook|reject|exclud',s,re.I):print('NEXT',s[:500].strip())
pat=re.compile(r'inverse.?Z|Grothendieck|q.?rook|Garsia|Aluffi|2507.01332',re.I)
with (L/'registry-selection.jsonl').open('w') as out:
 for name in ('omega','openai'):
  p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt.gz');frozen.append({'path':str(p),'sha256':digest(p)})
  n=hits=0
  with gzip.open(p,'rt') as f:
   for s in f:
    n+=1
    if pat.search(s):out.write(json.dumps({'registry':name,'record':s.strip()})+'\n');hits+=1;print(name,s[:300].strip())
  print('registry',name,n,hits)
 intervals=json.loads((B/'sol-renyi-registry-gap-closure-r3/intervals.json').read_text())
 print('interval structure',str(intervals)[:4500])
with (L/'frozen-before.json').open('w') as f:json.dump(frozen,f,indent=2)
if (L/'snippets.jsonl').exists():
 with (L/'snippets.jsonl').open() as f:
  shown=0
  for s in f:
   d=json.loads(s)
   if '/lanes/' in d['path'] and any(w in Path(d['path']).name.lower() for w in ('summary','discovery','proof','review')):
    print('ORIGINAL',d['path'],d['snippet'][:340]);shown+=1
    if shown>=25:break
