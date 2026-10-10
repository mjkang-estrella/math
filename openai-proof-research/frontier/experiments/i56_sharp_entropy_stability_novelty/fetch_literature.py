"""Optional live primary-source refresh. Refuses to overwrite a previous run."""
from pathlib import Path
import concurrent.futures,datetime,hashlib,json,subprocess,urllib.request,urllib.error
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i56_sharp_entropy_stability_novelty/literature'
def fetch(job):
 name,url=job; r={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I56 independent mathematical literature audit'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as e:
  b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e:
  r['error']=repr(e);return r
 ext='.pdf' if b.startswith(b'%PDF') else '.html';p=S/(name+ext);p.write_bytes(b);r.update(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if ext=='.pdf':
  t=p.with_suffix('.txt');a=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True);r['extraction']={'returncode':a.returncode,'stderr':a.stderr.decode(),'path':str(t.relative_to(ROOT)),'sha256':hashlib.sha256(t.read_bytes()).hexdigest() if t.exists() else None}
 return r
if __name__=='__main__':
 if (S/'manifest.json').exists():raise SystemExit('Refusing overwrite')
 S.mkdir(parents=True,exist_ok=True)
 jobs=[]
 for name,id in [('odeco','1512.08031'),('auddy-yuan','2007.09024'),('sroa','1705.10404'),('fk','1008.4002'),('fms','2406.07406'),('mnr','2309.01840'),('rademacher','1404.5662'),('kipp','2411.08722'),('kipp-platonic','2407.01353'),('biaggi','2206.01521')]:
  for kind in ['abs','pdf']:jobs.append((name+'-'+kind,'https://arxiv.org/'+kind+'/'+id))
 jobs.extend([('mnr-author','https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Melbourne-Nayar-Roberto.pdf'),('fms-author','https://perso.math.u-pem.fr/fradelizi.matthieu/pdf/entropy-slicing-mahler-2024-06-14.pdf'),('mnr-journal','https://link.springer.com/article/10.1007/s00440-025-01431-3'),('kipp-journal','https://link.springer.com/article/10.1007/s00454-026-00829-7')])
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:results=list(ex.map(fetch,jobs))
 (S/'manifest.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps([{k:r[k] for k in ['name','status','error','bytes'] if k in r} for r in results],indent=2))
