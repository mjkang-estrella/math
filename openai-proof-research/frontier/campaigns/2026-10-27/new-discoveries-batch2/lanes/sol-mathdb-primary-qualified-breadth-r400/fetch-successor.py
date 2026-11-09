from pathlib import Path
import urllib.request,datetime,hashlib,json,subprocess
O=Path(__file__).resolve().parent;(O/'evidence').mkdir(exist_ok=True); log=json.loads((O/'source-provenance.json').read_text())
urls=[('rbm-mixtures-author','https://arxiv.org/pdf/1709.05276v2')]
for name,url in urls:
 r={'name':name,'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   r.update(final_url=f.url,status=f.status);b=f.read(10000000)
  assert b.startswith(b'%PDF'), 'not PDF; stop, no extraction'
  p=O/'evidence'/f'{name}.pdf';p.write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),version='exact retained PDF; internal version to be read')
  log.append(r);(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:
  r['failure']=repr(e);log.append(r);(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
