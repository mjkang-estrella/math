from pathlib import Path
import subprocess,tempfile,json,hashlib
R=Path(__file__).resolve().parent;P=R/'primary'
for n in ['rivest','montgomery']:
 d=(P/n).read_bytes();assert hashlib.sha256(d).hexdigest()==json.loads((P/(n+'.meta.json')).read_text())['sha256']
 with tempfile.TemporaryDirectory(dir=R) as t:
  t=Path(t);p=t/(n+'.ppt');p.write_bytes(d)
  r=subprocess.run(['libreoffice','-env:UserInstallation='+ (t/'profile').as_uri(),'--headless','--convert-to','pdf','--outdir',str(P),str(p)],capture_output=True,text=True,timeout=60)
  (P/(n+'.conversion.json')).write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr},indent=2))
  assert r.returncode==0
 subprocess.run(['pdftotext','-layout',str(P/(n+'.pdf')),str(P/(n+'-converted.txt'))],check=True)
 print(n,'converted')
