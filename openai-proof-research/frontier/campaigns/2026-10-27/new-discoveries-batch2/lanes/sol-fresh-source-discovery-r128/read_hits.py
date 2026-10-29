from research import H,R,save
import json,collections
D=collections.defaultdict(set)
for l in (H/'matches.jsonl').open():
 try:x=json.loads(l)
 except:continue
 if x['key'] in ['domino-id','domino-title','partite-id','partite-title','spectral-title','spectral-authors']:D[x['key']].add(x['path'])
save('exact-hit-paths.json',{k:sorted(v) for k,v in D.items()})
for k,v in D.items():
 print(k,len(v))
 for p in sorted(v): print(p)
