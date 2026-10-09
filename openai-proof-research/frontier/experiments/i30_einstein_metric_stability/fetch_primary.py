from pathlib import Path
import urllib.request,hashlib,json,datetime,re,subprocess,concurrent.futures
S=Path('frontier/sources/i30_einstein_metric_stability/literature')
ids=['1202.2912','1808.03774','2109.02449','2008.09956','1312.2224','2102.12840','2408.11115']
def fetch(i):
 out=[]
 url='https://arxiv.org/abs/'+i
 b=urllib.request.urlopen(url,timeout=60).read();p=S/(i+'-abs.html');p.write_bytes(b)
 versions=re.findall(r'\[v(\d+)\]',b.decode());v=max(map(int,versions)) if versions else 1
 for name,u,raw in [(p.name,url,b),(f'{i}v{v}.pdf',f'https://arxiv.org/pdf/{i}v{v}',None)]:
  if raw is None: raw=urllib.request.urlopen(u,timeout=90).read()
  dest=S/name;dest.write_bytes(raw);out.append(dict(path=str(dest),url=u,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat(),version=v))
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],check=True)
 return out
rows=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=7) as ex:
 for i,r in zip(ids,ex.map(fetch,ids)):
  rows+=r;print(i,r[-1]['version'],r[-1]['bytes'],flush=True)
(S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
