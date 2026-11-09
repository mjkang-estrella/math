#!/usr/bin/env python3
import pathlib,json,urllib.request,hashlib,datetime
r=pathlib.Path(__file__).resolve().parents[1];o=r/'sources';receipts=json.loads((o/'receipts.json').read_text())
def get(name,u):
 rec=dict(url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'public-math-research/1.0'}),timeout=35) as f:b=f.read(16*1024*1024);rec['status']=f.status
  (o/name).write_bytes(b);rec.update(path='sources/'+name,sha256=hashlib.sha256(b).hexdigest());return json.loads(b) if name.endswith('.json') else b
 except Exception as e:
  rec['error']=str(e)
  if getattr(e,'code',0) in (403,429):raise SystemExit('STOP: access/rate limit; no further requests')
 finally:receipts.append(rec);(o/'receipts.json').write_text(json.dumps(receipts,indent=2))
for repo,dirs in [('openai/math',['preprints']),('the-omega-institute/trureturing',['Problems','D5/S3/Quantum/Matrix'])]:
 key=repo.split('/')[-1];sha=json.loads((o/(key+'-head.json')).read_text())['sha']
 for d in dirs:
  # contents API yields the subtree SHA without fetching another truncated recursive root
  data=get(key+'-'+d.replace('/','-')+'-contents.json',f'https://api.github.com/repos/{repo}/contents/{d}?ref={sha}')
  if not data:continue
  for item in data:
   p=item['path']
   if 'weighted' in p.lower() and any(s in p.lower() for s in ['bottcher','botcher','bw']):get(key+'-'+p.replace('/','-'),f'https://raw.githubusercontent.com/{repo}/{sha}/{p}')
get('trureturing-problem-history.json','https://api.github.com/repos/the-omega-institute/trureturing/commits?path=Problems/mayumi-kimura-ohno-chruscinski-2024-weighted-bottcher-wenzel-ii.md&per_page=10')
print('done')
