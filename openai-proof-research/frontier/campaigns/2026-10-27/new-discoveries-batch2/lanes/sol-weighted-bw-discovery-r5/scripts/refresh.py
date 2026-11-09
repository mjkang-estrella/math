#!/usr/bin/env python3
import urllib.request,json,hashlib,datetime,pathlib
root=pathlib.Path(__file__).resolve().parents[1]; out=root/'sources'; receipts=[]
def get(name,url):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'public-math-research/1.0'}),timeout=40) as r: b=r.read(16*1024*1024); status=r.status
  (out/name).write_bytes(b); receipts.append(dict(path='sources/'+name,url=url,utc=t,status=status,sha256=hashlib.sha256(b).hexdigest())); return b
 except Exception as e:
  receipts.append(dict(url=url,utc=t,error=str(e)))
  (root/'sources/receipts.json').write_text(json.dumps(receipts,indent=2))
  if getattr(e,'code',0) in (403,429):raise SystemExit('STOP: access/rate limit; no further requests')
  return None
for repo in ['openai/math','the-omega-institute/trureturing']:
 key=repo.split('/')[-1]; b=get(key+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
 if not b:continue
 sha=json.loads(b)['sha']; tree=get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
 if tree:
  data=json.loads(tree); paths=[x['path'] for x in data['tree'] if any(s in x['path'].lower() for s in ['bottcher','botcher','mayumi','weightedbw'])]; (out/(key+'-matches.json')).write_text(json.dumps({'head':sha,'truncated':data.get('truncated'),'paths':paths},indent=2))
  for k,p in enumerate(paths):
   if p.endswith('.md'):get(key+f'-body-{k}.md',f'https://raw.githubusercontent.com/{repo}/{sha}/{p}')
get('mathdb-362175.json','https://mathdb.com/api/posts/362175')
get('2403.04199v2.html','https://arxiv.org/html/2403.04199v2')
get('2610.29240.html','https://arxiv.org/html/2610.29240v1')
get('2610.08980.html','https://arxiv.org/html/2610.08980v1')
get('fang-cheng-openalex.json','https://api.openalex.org/works/https://doi.org/10.1016/j.laa.2025.03.015')
(root/'sources/receipts.json').write_text(json.dumps(receipts,indent=2));print(json.dumps(receipts,indent=2))
