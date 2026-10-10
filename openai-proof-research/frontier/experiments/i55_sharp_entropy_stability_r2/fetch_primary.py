"""Optional fresh primary retrieval; never overwrites an earlier manifest."""
from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i55_sharp_entropy_stability_r2/literature'
urls={
'odeco-abs':'https://arxiv.org/abs/1512.08031','odeco-v1':'https://arxiv.org/pdf/1512.08031v1',
'auddy-abs':'https://arxiv.org/abs/2007.09024','auddy-v2':'https://arxiv.org/pdf/2007.09024v2',
'sroa-abs':'https://arxiv.org/abs/1705.10404','sroa-v1':'https://arxiv.org/pdf/1705.10404v1',
'fk-abs':'https://arxiv.org/abs/1008.4002','fk-v2':'https://arxiv.org/pdf/1008.4002v2',
'fms-abs':'https://arxiv.org/abs/2406.07406','mnr-abs':'https://arxiv.org/abs/2309.01840',
'kipp-abs':'https://arxiv.org/abs/2411.08722','rademacher-abs':'https://arxiv.org/abs/1404.5662',
'fms-author':'https://perso.math.u-pem.fr/fradelizi.matthieu/pdf/entropy-slicing-mahler-2024-06-14.pdf'}
def sha(b):return hashlib.sha256(b).hexdigest()
def get(it):
 name,url=it; o={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I55 independent mathematical audit'}),timeout=35) as r:
   b=r.read();o.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
 except Exception as e:
  o['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):b=e.read();o['status']=e.code
  else:return o
 ext='.pdf' if b.startswith(b'%PDF') else '.html'; p=S/(name+ext); p.write_bytes(b);o.update(path=str(p.relative_to(R)),sha256=sha(b))
 if ext=='.pdf':
  r=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True); t=p.with_suffix('.txt');t.write_bytes(r.stdout);o['extraction']={'path':str(t.relative_to(R)),'sha256':sha(r.stdout),'returncode':r.returncode,'stderr':r.stderr.decode()}
 return o
if __name__=='__main__':
 if (S/'manifest.json').exists():raise SystemExit('Refusing to overwrite prior retrievals')
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: out=list(ex.map(get,urls.items()))
 (S/'manifest.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps([{k:v for k,v in o.items() if k in ('name','status','error','sha256')} for o in out],indent=2))
