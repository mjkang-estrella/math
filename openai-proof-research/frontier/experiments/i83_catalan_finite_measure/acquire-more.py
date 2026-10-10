from pathlib import Path
import urllib.request,urllib.error,json,hashlib,subprocess,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i83_catalan_finite_measure'
urls=[('brown-record.html','https://arxiv.org/abs/2604.20741'),('brown.pdf','https://arxiv.org/pdf/2604.20741'),('catalan-new-record.html','https://arxiv.org/abs/2609.04176'),('catalan-new.pdf','https://arxiv.org/pdf/2609.04176')]
with (S/'primary-requests-more.jsonl').open('w') as log:
 for name,url in urls:
  row={'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=45) as r:b=r.read();row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  except urllib.error.HTTPError as e:b=e.read();row.update(status=e.code,error=str(e),headers=dict(e.headers))
  except Exception as e:b=b'';row.update(status=None,error=repr(e))
  p=S/'primary'/name;p.write_bytes(b);row.update(local=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):
   o=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True);t=p.with_suffix('.pdf.txt');t.write_bytes(o.stdout);row['extraction']={'local':str(t.relative_to(R)),'sha256':hashlib.sha256(o.stdout).hexdigest(),'code':o.returncode,'stderr':o.stderr.decode()}
  log.write(json.dumps(row,sort_keys=True)+'\n');log.flush();print(name,row['status'],len(b))
