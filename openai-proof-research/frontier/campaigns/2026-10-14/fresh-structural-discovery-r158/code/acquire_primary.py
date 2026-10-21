from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158'); url='https://arxiv.org/src/math/0503137v3'
b=urllib.request.urlopen(url,timeout=45).read(); p=R/'private/primary'; p.mkdir(exist_ok=True); (p/'pp10-incoming.tar').write_bytes(b)
rec={'url':url,'incoming':{'size':len(b),'sha256':hashlib.sha256(b).hexdigest()},'members':[]}
try:
 t=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
 for x in t.getmembers():
  if x.isfile() and x.name.endswith(('.tex','.bbl','.bib')):
   data=t.extractfile(x).read(); name=x.name.replace('/','__'); (p/name).write_bytes(data)
   rec['members'].append({'original_member':x.name,'selected_copy':name,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
except tarfile.ReadError:
 data=gzip.decompress(b); (p/'pp10.tex').write_bytes(data); rec['members'].append({'selected_copy':'pp10.tex','size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(R/'private/primary-identities01.json').write_text(json.dumps(rec,indent=2)); print(rec)
