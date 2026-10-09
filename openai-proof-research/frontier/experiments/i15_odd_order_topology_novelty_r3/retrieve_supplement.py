from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i15_odd_order_topology_novelty_r3';L=S/'literature'
jobs=[('khan-connected-sums','https://qkhan.pages.iu.edu/research/ARTICLES/ConnectedSums4.pdf'),('hadziosmanovic-mangioni','https://arxiv.org/pdf/2605.23829'),('metadata-2605.23829','https://arxiv.org/abs/2605.23829')]
a=[]
for name,url in jobs:
 rec={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as f:b=f.read();rec.update(final_url=f.url,status_code=f.status)
  ext='html' if name.startswith('metadata') else 'pdf';p=L/(name+'.'+ext);p.write_bytes(b);rec.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),status='ok')
  if ext=='pdf':
   assert b.startswith(b'%PDF');q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);rec.update(text_path=str(q.relative_to(R)),text_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 except Exception as e:rec.update(status='error',error=repr(e))
 a.append(rec)
(S/'supplement-retrieval-manifest.json').write_text(json.dumps(a,indent=2)+'\n');print([(r['name'],r['status']) for r in a])
