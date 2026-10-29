from pathlib import Path
import re,json,hashlib,urllib.request,datetime
P=Path(__file__).resolve().parent; root=next(x for x in P.parents if x.name=='openai-proof-research')
terms=re.compile(r'melonic|clasped|2503\.16296|367609|2502\.08948|2509\.16868|Ishii|Links.Gould|gamma.polynomial',re.I)
files=[];hits=[]
for f in root.rglob('*'):
 if not f.is_file() or P in f.parents:continue
 if not (any(s in f.name.lower() for s in ['summary','discovery','findings','proof','review','ledger']) and f.suffix in ['.md','.json','.txt']):continue
 b=f.read_bytes();files.append(dict(path=str(f.relative_to(root)),sha256=hashlib.sha256(b).hexdigest()))
 s=b.decode(errors='replace')
 for i,l in enumerate(s.splitlines(),1):
  if terms.search(l):hits.append(dict(path=str(f.relative_to(root)),line=i,text=l[:800]))
(P/'duplicate-audit.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=files,hits=hits),indent=2))
print('all-date files',len(files),'hits',len(hits));print(json.dumps(hits[:12],indent=2))
# registry fresh HEAD already fetched; read current compare from supplied baseline, never Git
log=json.loads((P/'http.json').read_text())
urls={'banana_v2':'https://arxiv.org/html/2503.16296v2','melonic_abs':'https://arxiv.org/abs/2007.08565','melonic':'https://arxiv.org/html/2007.08565','banana_mathdb':'https://mathdb.com/p/367609','omega_delta': 'https://api.github.com/repos/the-omega-institute/trureturing/compare/d2b0ee6e958cf646530d3476088494e349570b46...'+json.loads((P/'sources/omega_head.json').read_text())['sha']}
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit'}),timeout=25) as r:b=r.read();status=r.status
  fn='sources/'+name+('.json' if 'api.github' in url else '.html');(P/fn).write_bytes(b);log.append(dict(name=name,url=url,status=status,file=fn,sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:log.append(dict(name=name,url=url,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log[-5:],indent=2))
for name in ['omega','openai']:print(name,json.loads((P/('sources/'+name+'_head.json')).read_text())['sha'])
