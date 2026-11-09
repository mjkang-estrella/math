from pathlib import Path
import urllib.request,json,hashlib,datetime
p=Path(__file__).resolve().parent
routes=[('omega-deb-sokal.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/83b70a1d0d6a58bb32521c741805d845d401c5f8/D5/S0/Certificates/DebSokalConjectureFourRefutation.lean'),('omega-symmetry.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/83b70a1d0d6a58bb32521c741805d845d401c5f8/D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization.lean'),('omega-jensen.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/83b70a1d0d6a58bb32521c741805d845d401c5f8/D5/S3/Zeros/Jensen/JensenPolynomialObstruction.lean'),('openai-noncoordinate.tex','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026/build/paper.tex')]
rr=[]
for name,url in routes:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:
   b=f.read(2000000);(p/name).write_bytes(b);r.update(status=f.status,file=name,sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['error']=str(e)
 rr.append(r); print(r,flush=True)
(p/'registry-body-receipts.json').write_text(json.dumps(rr,indent=2))
