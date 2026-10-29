import json,gzip,sys
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
if sys.argv[1]=='context':
 for n in ['ledger.json','prior-campaign-context.json']:
  j=json.loads((L.parent.parent/n).read_text())
  print(n)
  for k,v in j.items():
   if isinstance(v,list):
    print(k,len(v))
    for x in v:
     if isinstance(x,dict):print({a:x[a] for a in ['number','title','source_target','reason'] if a in x})
   elif not isinstance(v,dict):print(k,str(v)[:300])
elif sys.argv[1]=='matches':
 refined=len(sys.argv)>2 and sys.argv[2]=='refined'
 hits=[json.loads(x) for x in (L/('refined-matches.jsonl' if refined else 'target-matches.jsonl')).read_text().splitlines()]
 hashes={x['sha256'] for x in hits};aliases=[]
 with gzip.open(L/'pathmap.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line)
   if h in hashes:aliases.append([h,p])
 (L/('refined-aliases.json' if refined else 'target-aliases.json')).write_text(json.dumps(aliases,indent=2)+'\n')
 for h,p in aliases:
  if any(z in p for z in ['SUMMARY.md','discovery.md','DECISION.md','rejection','review.md']):print(p)
 print('distinct hits',len(hits),'aliases',len(aliases))
