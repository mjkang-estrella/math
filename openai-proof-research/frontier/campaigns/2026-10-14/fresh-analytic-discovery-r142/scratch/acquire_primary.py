from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip
R=Path.cwd(); out=[]
for name,ver in [('barthe-milman','1202.5318v1'),('milman-curvature','0902.1560v2'),('bizeul','2306.12997v3')]:
 url='https://arxiv.org/src/'+ver; rec={'name':name,'version':ver,'url':url}
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); d=R/'private/primary'/name; d.mkdir(parents=True,exist_ok=True); (d/'raw').write_bytes(b)
  rec.update(size=len(b),sha256=hashlib.sha256(b).hexdigest(),raw=str((d/'raw').relative_to(R)),members=[])
  try:
   with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tf:
    for m in tf.getmembers():
     if not m.isfile() or not m.name.endswith(('.tex','.bib','.bbl')): continue
     p=Path(m.name)
     if p.is_absolute() or '..' in p.parts: raise ValueError('unsafe member')
     bb=tf.extractfile(m).read(); dest=d/'extracted'/p; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(bb); rec['members'].append({'name':m.name,'local':str(dest.relative_to(R)),'size':len(bb),'sha256':hashlib.sha256(bb).hexdigest()})
   rec['format']='tar'
  except tarfile.ReadError:
   bb=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
   dest=d/'extracted.tex'; dest.write_bytes(bb); rec['format']='gzip-single' if b[:2]==b'\x1f\x8b' else 'single';rec['members'].append({'name':'extracted.tex','local':str(dest.relative_to(R)),'size':len(bb),'sha256':hashlib.sha256(bb).hexdigest()})
  print(name,rec['format'],[(x['name'],x['size']) for x in rec['members']],flush=True)
 except Exception as e: rec['error']=repr(e); print(name,repr(e),flush=True)
 out.append(rec)
(R/'primary-authentication.json').write_text(json.dumps(out,indent=2))
