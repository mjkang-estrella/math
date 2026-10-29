from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path(__file__).resolve().parent;log=[]
urls=[('zones.pdf','https://arxiv.org/pdf/1703.10550'),('plank.pdf','https://arxiv.org/pdf/1906.04126'),('cyclemath.tex','https://raw.githubusercontent.com/cyclemath/great-subspheres-gaussian-minima/main/convex_hulls_great_subspheres_gaussian_minima_v0.1.tex'),('local-stability.html','https://www.evidencepress.org/releases/gaussian-cosine-local-stability/'),('registry-softminimum.lean','https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean'),('registry-cdso.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/73a5033dd654a16a14fcd1b13277f1a03d81d826/docs/develop/theory/CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md')]
for name,url in urls:
 row={'file':'sources/'+name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read(18000000);row.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/name).write_bytes(b)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:row['error']=repr(e)
 log.append(row);(P/'more-http.json').write_text(json.dumps(log,indent=2));print(row)
