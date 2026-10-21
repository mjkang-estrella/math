from pathlib import Path,PurePosixPath
import urllib.request,hashlib,json,tarfile,io,gzip
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147')
records=[]
for ident in ['1211.2341v1','1209.5640v2']:
 url='https://arxiv.org/src/'+ident
 b=urllib.request.urlopen(url,timeout=45).read(); raw=R/'private/primary'/f'{ident}.source';raw.write_bytes(b)
 item={'url':url,'version':ident,'incoming_path':str(raw.relative_to(R)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'selected':[]}
 try:
  ar=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
  members=[(m.name,ar.extractfile(m).read()) for m in ar.getmembers() if m.isfile() and not m.issym() and not m.islnk() and PurePosixPath(m.name).suffix in ['.tex','.bbl','.bib'] and not PurePosixPath(m.name).is_absolute() and '..' not in PurePosixPath(m.name).parts]
 except tarfile.ReadError:
  body=gzip.decompress(b) if b.startswith(b'\x1f\x8b') else b;members=[('main.tex',body)]
 for name,body in members:
  dst=R/'private/primary'/ident/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(body)
  item['selected'].append({'member':name,'copy':str(dst.relative_to(R)),'size':len(body),'sha256':hashlib.sha256(body).hexdigest()})
 records.append(item);print(ident,[(a['member'],a['size']) for a in item['selected']])
(R/'PRIMARY-AUTH.json').write_text(json.dumps(records,indent=2)+'\n')
