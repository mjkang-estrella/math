import json,hashlib,datetime,urllib.request,urllib.error,resource,concurrent.futures
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(500*1024**2,500*1024**2))
OUT=Path(__file__).parent/'evidence';OUT.mkdir(exist_ok=True)
receipts=[]
def fetch(name,url):
 start=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Jacobi-independent-review/1.0 (public read-only research)','Accept':'application/vnd.github+json' if 'api.github.com' in url else '*/*'})
  with urllib.request.urlopen(req,timeout=40) as res:
   raw=res.read(12*1024**2+1);assert len(raw)<=12*1024**2
   row=dict(name=name,url=url,final_url=res.url,status=res.status,utc=start,response_date=res.headers.get('Date'),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
  (OUT/name).write_bytes(raw)
 except Exception as e: row=dict(name=name,url=url,utc=start,error=str(e))
 receipts.append(row);return row
jobs=[('primary-abs.html','https://arxiv.org/abs/2608.23006'),('primary.html','https://arxiv.org/html/2608.23006v2'),('companion-abs.html','https://arxiv.org/abs/2609.29531'),('companion.html','https://arxiv.org/html/2609.29531v2'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 for row in pool.map(lambda x:fetch(*x),jobs): print(json.dumps(row))
for short,repo,dirs,cat in [('openai','openai/math',['preprints'],'CONTENTS.md'),('omega','the-omega-institute/trureturing',['Problems','D5','Blueprint'],'README.md')]:
 head=json.loads((OUT/(short+'-head.json')).read_bytes());sha=head['sha'];print(short,sha,head['commit']['committer']['date'])
 root=fetch(short+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha)
 if 'error' in root:continue
 entries=json.loads((OUT/(short+'-root.json')).read_bytes())['tree']
 for d in dirs:
  ent=next(x for x in entries if x['path']==d)
  row=fetch(short+'-'+d+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+ent['sha']+'?recursive=1');print(json.dumps(row))
  if 'error' not in row:
   tree=json.loads((OUT/row['name']).read_bytes());print(d,'entries',len(tree['tree']),'truncated',tree['truncated'])
 print(json.dumps(fetch(short+'-'+cat,'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+cat)))
(OUT/'retrieval.json').write_text(json.dumps(receipts,indent=2)+'\n')
