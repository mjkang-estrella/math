from pathlib import Path
import hashlib,urllib.request,tarfile,io,gzip,json
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153'); out=[]
for key,version in [('ccl','2102.12840v3'),('dlt','1003.3527v2')]:
 url='https://arxiv.org/src/'+version;b=urllib.request.urlopen(url,timeout=45).read();dst=R/'private/primary'/key;dst.mkdir(parents=True,exist_ok=True);(dst/'incoming.bin').write_bytes(b)
 rec={'key':key,'version':version,'url':url,'incoming':{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'selected':[]}
 try:
  tf=tarfile.open(fileobj=io.BytesIO(b),mode='r:*');members=[(m.name,tf.extractfile(m).read()) for m in tf.getmembers() if m.isfile() and m.name.endswith(('.tex','.bib'))]
 except tarfile.ReadError:
  members=[('main.tex',gzip.decompress(b) if b.startswith(b'\x1f\x8b') else b)]
 for n,data in members:
  if '..' in Path(n).parts or Path(n).is_absolute(): raise ValueError(n)
  p=dst/'selected'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);rec['selected'].append({'member':n,'path':str(p.relative_to(R)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 out.append(rec);print(key,'selected',[(n,len(data)) for n,data in members])
(R/'PRIMARY-AUTH.json').write_text(json.dumps(out,indent=2)+'\n')
