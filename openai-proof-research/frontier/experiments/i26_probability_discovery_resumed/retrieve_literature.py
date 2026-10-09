"""Retain exact primary bytes; network retrieval is not a reproducibility test."""
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, re, subprocess, urllib.request, sys
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i26_probability_discovery_resumed/literature'
S.mkdir(exist_ok=True)
IDS={'schramm':'math/0602151','ss-discrete':'math/0605337','ss-continuum':'1008.2447','miller':'1010.1356','glazman-manolescu':'1810.05592','glazman-lammers':'2306.01527','vanneuville':'1906.12256','poisson-spectra':'2407.13502','sixvertex':'2603.06268','davis-cardy':'cond-mat/9911083','dotsenko':'hep-th/9501017'}
def get(url):
 req=urllib.request.Request(url,headers={'User-Agent':'research-source-comparison/1.0'})
 with urllib.request.urlopen(req,timeout=45) as f:return f.read(),f.geturl(),dict(f.headers)
def job(k,id):
 out=[]
 try:
  b,u,headers=get('https://arxiv.org/abs/'+id)
  (S/(k+'-abs.html')).write_bytes(b)
  versions=re.findall(re.escape(id)+r'v(\d+)',b.decode(errors='replace'))
  v=max(map(int,versions)) if versions else 1
  for ext,url in [('html','https://arxiv.org/abs/'+id),('pdf','https://arxiv.org/pdf/'+id+'v'+str(v))]:
   if ext=='pdf':b,u,headers=get(url)
   name=k+('-abs.html' if ext=='html' else '.pdf');(S/name).write_bytes(b)
   out.append(dict(name=name,url=url,final_url=u,arxiv_version=v,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),headers=headers))
  subprocess.run(['pdftotext','-layout',str(S/(k+'.pdf')),str(S/(k+'.txt'))],check=True)
 except Exception as e:out.append(dict(name=k,error=repr(e)))
 return out
if len(sys.argv)>1: IDS={k:IDS[k] for k in sys.argv[1:]}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
 result=[x for group in pool.map(lambda item:job(*item),IDS.items()) for x in group]
prior=json.loads((S/'retrieval-manifest.json').read_text()) if (S/'retrieval-manifest.json').exists() else []
names={x['name'] for x in result}
(S/'retrieval-manifest.json').write_text(json.dumps([x for x in prior if x['name'] not in names]+result,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k in ['name','bytes','arxiv_version','error']} for x in result],indent=2))
