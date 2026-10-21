from pathlib import Path
import urllib.request,hashlib,json,gzip,tarfile,io
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157')
# Explicit primary versions in the one selected family. All incoming bytes stay private.
items=[('barkley-gaetz','https://arxiv.org/src/2404.04246v3'),('braden-macpherson','https://arxiv.org/src/math/0008200v2')]
out=[]
for name,url in items:
 rec={'name':name,'url':url}
 try:
  b=urllib.request.urlopen(url,timeout=30).read();p=R/'private'/name;p.mkdir();(p/'incoming.bin').write_bytes(b)
  rec.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),selected=[])
  raw=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
  try:
   t=tarfile.open(fileobj=io.BytesIO(raw))
   for m in t.getmembers():
    if not m.isfile() or not m.name.endswith(('.tex','.bib','.bbl')):continue
    # select text by explicit archive membership, never filesystem extraction
    data=t.extractfile(m).read();dest=p/('text'+str(len(rec['selected']))+Path(m.name).suffix);dest.write_bytes(data)
    rec['selected'].append({'member':m.name,'path':str(dest.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
  except tarfile.ReadError:
   dest=p/'text0.tex';dest.write_bytes(raw);rec['selected'].append({'member':'single gzip/plain source','path':str(dest.relative_to(R)),'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
 except Exception as e:rec['failure']=repr(e)
 out.append(rec)
(R/'private/primary-incoming01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
