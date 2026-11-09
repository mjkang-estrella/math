from pathlib import Path
import json,hashlib,urllib.request,datetime,subprocess
O=Path(__file__).parent;L=O.parent
bind=json.loads((O/'flat-bindings.json').read_text())
def binding(p):
 d=p.read_bytes();return {'path':str(p.resolve()),'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)}
for p in [L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-fresh-discrete-discovery-r6/sources/2108.13537v1.txt',L/'sol-fresh-discrete-discovery-r6/sources/2108.13537v1.html']:bind.append(binding(p))
(O/'flat-bindings.json').write_text(json.dumps(bind,indent=2)+'\n')
prov=[]
for a in ['2112.00444','2203.07227','2205.09902','2112.03338','2201.01352','2107.11160']:
 url='https://arxiv.org/pdf/'+a+'v1';p=O/(a+'v1.pdf');row={'url':url,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':'generic Python urllib default; no personal data'}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:d=r.read();row['final_url']=r.url
  assert d.startswith(b'%PDF');p.write_bytes(d);row['pdf']=binding(p)
  # Persist byte binding BEFORE extraction.
  prov.append(row);(O/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);row['text']=binding(t)
 except Exception as e:
  row['failure']=str(e)
  if row not in prov:prov.append(row)
 (O/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print(json.dumps(prov,indent=2))
