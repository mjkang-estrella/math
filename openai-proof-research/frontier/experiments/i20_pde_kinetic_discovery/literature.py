from pathlib import Path
import concurrent.futures, requests, hashlib, json, datetime, subprocess
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i20_pde_kinetic_discovery/literature'
OUT.mkdir(parents=True,exist_ok=True)
SOURCES=[('bgss','https://arxiv.org/pdf/2008.10403v3'),('pss','https://arxiv.org/pdf/1301.2514v2'),('instability','https://arxiv.org/pdf/2606.01331v3'),('dhm','https://arxiv.org/pdf/2408.07818v2'),('correlation','https://arxiv.org/pdf/1405.4676v3'),('lebihan','https://arxiv.org/pdf/2408.03597v2'),('bgss_v2','https://arxiv.org/pdf/2008.10403v2'),('correlation_v2','https://arxiv.org/pdf/1405.4676v2'),('dhm_v3','https://arxiv.org/pdf/2408.07818v3'),('georgii','https://www.mathematik.uni-muenchen.de/~georgii/papers/FKGrev.pdf'),('onesided','https://arxiv.org/pdf/1612.03722v1')]
def get(item):
 name,url=item
 r=requests.get(url,timeout=60)
 row={'id':name,'url':url,'final_url':r.url,'http_status':r.status_code,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 ext='pdf' if r.content.startswith(b'%PDF') else 'response'
 p=OUT/(name+'.'+ext);p.write_bytes(r.content)
 row.update(path=str(p.relative_to(ROOT)),bytes=len(r.content),sha256=hashlib.sha256(r.content).hexdigest())
 if ext=='pdf':
  txt=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(txt)],check=True)
  row.update(text_path=str(txt.relative_to(ROOT)),text_sha256=hashlib.sha256(txt.read_bytes()).hexdigest(),header=txt.read_text()[:1500])
 return row
old=json.loads((OUT/'manifest.json').read_text()) if (OUT/'manifest.json').exists() else []
done={r['url'] for r in old}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
 rows=old+list(ex.map(get,[r for r in SOURCES if r[1] not in done]))
(OUT/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in rows:print(r['id'],r['http_status'],r['bytes'],r.get('header','')[:180].replace('\n',' '))
