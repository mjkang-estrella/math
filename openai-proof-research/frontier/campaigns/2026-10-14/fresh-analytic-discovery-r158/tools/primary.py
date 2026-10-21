from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r158/private/primary')
def one(ident):
 d=R/ident;d.mkdir(exist_ok=True);url='https://arxiv.org/src/'+ident
 rec={'id':ident,'url':url,'selected':[]}
 try:
  b=urllib.request.urlopen(url,timeout=45).read();(d/'incoming').write_bytes(b);rec['incoming']={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  try:
   tar=tarfile.open(fileobj=io.BytesIO(b));members=[m for m in tar.getmembers() if m.isfile() and m.name.lower().endswith(('.tex','.bib'))]
   for i,m in enumerate(members):
    data=tar.extractfile(m).read();name=f'{i:02d}-'+Path(m.name).name;(d/name).write_bytes(data);rec['selected'].append({'member':m.name,'copy':name,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
  except tarfile.ReadError:
   data=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b;(d/'source.tex').write_bytes(data);rec['selected'].append({'member':'single source','copy':'source.tex','size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:rec=list(pool.map(one,['1703.03635v1','2203.15731v3','2601.14411v1','2609.22035v1']))
(R/'auth.json').write_text(json.dumps(rec,indent=2)+'\n')
for r in rec:print(r['id'],[(m['copy'],m['size']) for m in r['selected']],r.get('error',''))
