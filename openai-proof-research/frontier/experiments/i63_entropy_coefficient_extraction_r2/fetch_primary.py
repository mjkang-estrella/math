"""One-shot primary retrieval, never part of read-only verification."""
from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,subprocess,re,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i63_entropy_coefficient_extraction_r2';D=S/'primary';D.mkdir(exist_ok=True)
assert not (D/'manifest.json').exists()
refs={'bk':'2608.31000','kitaev':'2405.02434','fk':'1008.4002','cpv':'0810.0812','bdhr':'1512.08031','bds':'2206.01521','robeva':'1409.6685','auddy':'2007.09024'}
jobs=[(name+'-abs','https://arxiv.org/abs/'+aid,'.html') for name,aid in refs.items()]+[(name+'-pdf','https://arxiv.org/pdf/'+aid,'.pdf') for name,aid in refs.items()]
jobs += [('bds-journal','https://rendiconti.dmi.units.it/volumi/54/017.pdf','.pdf'),('poinsot','https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf','.pdf')]
for i,row in enumerate(json.loads((S/'pins.json').read_text())):
 if row['upstream_path'].endswith(('transport.tex','matrix.tex','10_unital_averaging.tex')):jobs.append(('pin-'+str(i),'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+urllib.parse.quote(row['upstream_path']),'.tex'))
def one(j):
 name,url,ext=j;r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I63 mathematical proof review'}),timeout=40) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  p=D/(name+ext);p.write_bytes(b);r.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if ext=='.pdf':
   cp=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True);t=D/(name+'.txt');t.write_bytes(cp.stdout);r.update(text_path=str(t.relative_to(R)),text_sha256=hashlib.sha256(cp.stdout).hexdigest(),pdf_stderr=cp.stderr.decode(errors='replace'))
   match=re.search(rb'arXiv:[0-9.]+v\d+[^\n]*',cp.stdout);r['served_version']=match.group().decode() if match else None
 except Exception as e:r['error']=repr(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(one,jobs))
(D/'manifest.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
print(json.dumps([{'name':r['name'],'status':r.get('status'),'version':r.get('served_version'),'error':r.get('error')} for r in rows],indent=2))
