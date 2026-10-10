"""Historical I96 capture. Never invoked by verification. Writes owned paths only."""
from pathlib import Path
import json,hashlib,re,subprocess,urllib.request,datetime,concurrent.futures
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i96_finite_cat0_obstruction_novelty_r3'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def fetch(item):
 name,url=item;p=S/'primary'/name
 rec={'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local':p.relative_to(R).as_posix()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I96 mathematical primary-source comparison'}),timeout=45) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=sha(b));p.write_bytes(b)
  if b.startswith(b'%PDF'):
   t=p.with_suffix('.txt');out=subprocess.check_output(['pdftotext','-layout',str(p),'-']);t.write_bytes(out);rec.update(text=t.relative_to(R).as_posix(),text_sha256=sha(out))
 except Exception as e:rec['error']=str(e)
 return rec
def primaries():
 (S/'primary').mkdir(exist_ok=True)
 urls=[('ann.pdf','https://numdam.org/item/10.24033/asens.2363.pdf'),('kn.pdf','https://www2.mathematik.tu-darmstadt.de/~kohlenbach/cat-kappa.pdf'),('sturm.pdf','https://www.iam.uni-bonn.de/fileadmin/WT/Inhalt/people/Karl-Theodor_Sturm/papers/paper41.pdf'),('bridson.pdf','https://people.maths.ox.ac.uk/bridson/papers/BATH97.pdf')]
 for name,id in [('toyoda-six','2411.13877'),('toyoda-ann','2404.13871'),('toyoda-five','1907.09074'),('proximal','1707.09169'),('toyoda-fixed','1102.0729')]:
  urls.extend([(name+'.html','https://arxiv.org/abs/'+id),(name+'.pdf','https://arxiv.org/pdf/'+id)])
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:res=list(ex.map(fetch,urls))
 save(S/'primary/responses.json',res)
 print(json.dumps([{k:r[k] for k in ('local','status','error','bytes') if k in r} for r in res]))
def search():
 D=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
 qs=[{'name':'geometry','pattern':r'CAT\s*\(?-?\s*0|CAT\{0\}|CAT\(0\)|\\CAT|Reshetnyak|quasilinearization|reverse.median|parallel.set|Fano'}, {'name':'energy','pattern':r'Izeki|Nayatani|inductive.mean|nonlinear.spectral.gap|random.group|barycent|energy.contraction'}, {'name':'effective','pattern':r'proof.mining|quantitative.flat|effective.flat|finite.metric.inequal|quadratic.metric.inequal|metric.certificate|finite.CAT'}]
 pats=[re.compile(q['pattern'],re.I) for q in qs];hits=[[] for q in qs]
 for d in sorted(D,key=lambda d:d['path']):
  b=(R/d['local']).read_bytes();assert sha(b)==d['sha256']
  for n,l in enumerate(b.decode(errors='replace').splitlines(),1):
   for i,p in enumerate(pats):
    if p.search(l):hits[i].append({'path':d['path'],'local':d['local'],'line':n,'text':l})
 for q,h in zip(qs,hits):
  q.update(count=len(h),output=(S/(q['name']+'.json')).relative_to(R).as_posix());save(R/q['output'],h)
 save(S/'searches.json',qs)
 inv=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R).decode().splitlines();(S/'corpus-rg-files.txt').write_text('\n'.join(sorted(inv))+'\n')
 summary={q['name']:sorted(set(h['path'].split('/')[1] for h in hs)) for q,hs in zip(qs,hits)};save(S/'search-family-index.json',summary)
 print(json.dumps({q['name']:q['count'] for q in qs}));print(json.dumps(summary['effective'],indent=2))
if __name__=='__main__':
 import sys
 assert not (S/'seal-v1.json').exists()
 {'primaries':primaries,'search':search}[sys.argv[1]]()
