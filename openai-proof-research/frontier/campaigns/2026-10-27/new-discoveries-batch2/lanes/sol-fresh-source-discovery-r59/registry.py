from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent
names=['omega-D5.json','omega-Problems.json','openai-preprints.json','aim-tree.json','count-tree.json']
rows=[]
for n in names:
 f=L/'sol-fresh-source-discovery-r57'/'sources'/n
 if not f.exists():f=L/'sol-fresh-source-discovery-r56'/'sources'/n
 d=json.loads(f.read_text());hits=[x for x in d.get('tree',[]) if any(k in x['path'].lower() for k in ['rook','ferrers','aluffi','snake','grothendieck-class'])]
 rows.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'entries':len(d.get('tree',[])),'truncated':d.get('truncated'),'hits':hits})
# Preserve exact inherited failed calls. Do not retry API or use an alternative to bypass rate limiting.
f=L/'sol-fresh-source-discovery-r58'/'http.jsonl'
fails=[json.loads(l) for l in f.read_text().splitlines() if 'api.github.com' in l and 'error' in json.loads(l)]
(P/'registry-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FRESHNESS HOLD; dated scoped caches only','scopes':rows,'inherited_failed_requests':fails,'current_head_from_r58':'6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3','novelty_pass':False},indent=2)+'\n')
for r in rows:print(r['path'],r['entries'],[x['path'] for x in r['hits'] if not '/Brooks/' in x['path']])
print('INHERITED FAILURES',fails)
