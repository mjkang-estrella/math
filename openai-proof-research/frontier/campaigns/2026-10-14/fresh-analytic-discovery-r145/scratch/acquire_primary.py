from pathlib import Path,PurePosixPath
import urllib.request,hashlib,json,tarfile,io,gzip
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145');rows=[]
for ident in ['1805.00880v1','2210.07830v2','2208.14762v1','1907.08425v1','1805.00417v1']:
 url='https://arxiv.org/src/'+ident
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); d=R/'private/primary'/ident;d.mkdir(parents=True,exist_ok=True);(d/'incoming.bin').write_bytes(b)
  row={'id':ident,'url':url,'incoming_size':len(b),'incoming_sha256':hashlib.sha256(b).hexdigest(),'members':[]}
  try:
   with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as t:
    for m in t.getmembers():
     p=PurePosixPath(m.name)
     if m.isfile() and not p.is_absolute() and '..' not in p.parts and p.suffix in ['.tex','.bib','.bbl']:
      v=t.extractfile(m).read();f=d/'selected'/str(p);f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(v);row['members'].append({'archive_member':m.name,'selected_path':str(f.relative_to(R)),'size':len(v),'sha256':hashlib.sha256(v).hexdigest()})
  except tarfile.ReadError:
   v=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
   v.decode('utf8');f=d/'selected.tex';f.write_bytes(v);row['members'].append({'archive_member':None,'selected_path':str(f.relative_to(R)),'size':len(v),'sha256':hashlib.sha256(v).hexdigest()})
  rows.append(row);print(ident,[(v['selected_path'],v['size']) for v in row['members']],flush=True)
 except Exception as e:rows.append({'id':ident,'url':url,'failure':str(e)});print(ident,str(e),flush=True)
(R/'PRIMARY-AUTH.json').write_text(json.dumps(rows,indent=2)+'\n')
