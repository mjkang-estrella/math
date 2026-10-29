exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('r=[]')[0])
r=json.loads((L/'http.json').read_text())
for name,path in [('crown-proof.md','Blueprint/D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.md'),('crown-scalar.md','Blueprint/D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar.md')]:
 url='https://raw.githubusercontent.com/the-omega-institute/trureturing/549177fd878744e25dce688cbf94dc2955e8958f/'+path;x={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(2000000);x['status']=f.status
  (L/'sources'/name).write_bytes(b);x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:x['error']=str(e)
 r.append(x)
(L/'http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r[-2:],indent=2))
