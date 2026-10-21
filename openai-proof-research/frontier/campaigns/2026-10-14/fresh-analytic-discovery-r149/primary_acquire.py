from pathlib import Path
import urllib.request,hashlib,json,tarfile,io,gzip,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r149')
ids=['2109.05984v2','1301.5032v2','2609.10478v2']
def get(id):
 url='https://arxiv.org/src/'+id
 try:
  with urllib.request.urlopen(url,timeout=45) as res:b=res.read()
 except Exception as e:return {'id':id,'url':url,'failure':str(e)}
 folder=R/'private/primary'/id;folder.mkdir(parents=True,exist_ok=True);(folder/'incoming.bin').write_bytes(b)
 rec={'id':id,'url':url,'incoming_size':len(b),'incoming_sha256':hashlib.sha256(b).hexdigest(),'members':[]}
 try:
  with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tf:
   for m in tf.getmembers():
    if not m.isfile() or not m.name.endswith(('.tex','.bib')):continue
    data=tf.extractfile(m).read(); n=Path(m.name)
    if n.is_absolute() or '..' in n.parts:raise ValueError('unsafe member')
    p=folder/'selected'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    rec['members'].append({'member':m.name,'selected_path':str(p.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 except tarfile.ReadError:
  data=gzip.decompress(b) if b[:2]==b'\x1f\x8b' else b
  p=folder/'selected-main.tex';p.write_bytes(data)
  rec['members'].append({'member':'single decompressed source','selected_path':str(p.relative_to(R)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:recs=list(ex.map(get,ids))
(R/'PRIMARY-AUTH.json').write_text(json.dumps(recs,indent=2)+'\n')
for r in recs:
 print(r['id'],r.get('failure',r.get('incoming_size')))
 for x in r.get('members',[]):print(x['selected_path'],x['size'])
