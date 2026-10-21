from pathlib import Path,PurePosixPath
import urllib.request,json,hashlib,tarfile,io,gzip
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146'); records=json.loads((r/'PRIMARY-AUTH.json').read_text())
for ident in ['1510.00961v3']:
 url='https://arxiv.org/src/'+ident
 dest=r/'private/primary'/ident;dest.mkdir(parents=True,exist_ok=True)
 rec=dict(id=ident,url=url,selected=[])
 try:
  b=urllib.request.urlopen(url,timeout=50).read();(dest/'incoming.bin').write_bytes(b)
  rec.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
  try:
   with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as t:
    for m in t.getmembers():
     p=PurePosixPath(m.name)
     if not m.isfile() or p.is_absolute() or '..' in p.parts or p.suffix not in ['.tex','.bib','.bbl']:continue
     bb=t.extractfile(m).read();o=dest/'selected'/str(p);o.parent.mkdir(parents=True,exist_ok=True);o.write_bytes(bb)
     rec['selected'].append(dict(member=str(p),size=len(bb),sha256=hashlib.sha256(bb).hexdigest()))
  except tarfile.ReadError:
   bb=gzip.decompress(b) if b.startswith(b'\x1f\x8b') else b
   (dest/'selected.tex').write_bytes(bb);rec['selected'].append(dict(member='single decompressed body',size=len(bb),sha256=hashlib.sha256(bb).hexdigest()))
  print(ident,len(rec['selected']),len(b))
 except Exception as e:
  rec['failure']=str(e);print(ident,str(e))
 records.append(rec)
 (r/'PRIMARY-AUTH.json').write_text(json.dumps(records,indent=2)+'\n')
