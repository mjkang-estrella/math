"""One-time acquisition; NEVER called by offline verifier."""
from pathlib import Path
import json,hashlib,urllib.request,urllib.error,datetime,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i83_catalan_finite_measure'
def sha(b):return hashlib.sha256(b).hexdigest()
for f in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:
 p=S/'ledgers'/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/f).read_bytes())
urls=[('cdt-v2.pdf','https://arxiv.org/pdf/2408.15403v2'),('cdt-record.html','https://arxiv.org/abs/2408.15403'),('eskandari-record.html','https://arxiv.org/abs/2609.26354'),('zudilin-record.html','https://arxiv.org/abs/1507.05697')]
with (S/'primary-requests.jsonl').open('w') as log:
 for name,url in urls:
  row={'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=45) as resp:b=resp.read();row.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
  except urllib.error.HTTPError as e:b=e.read();row.update(status=e.code,error=str(e),headers=dict(e.headers))
  except Exception as e:b=b'';row.update(status=None,error=repr(e))
  p=S/'primary'/name;p.write_bytes(b);row.update(local=str(p.relative_to(R)),sha256=sha(b),bytes=len(b))
  if b.startswith(b'%PDF'):
   out=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True);t=p.with_suffix('.pdf.txt');t.write_bytes(out.stdout);row['extraction']={'local':str(t.relative_to(R)),'sha256':sha(out.stdout),'code':out.returncode,'stderr':out.stderr.decode()}
  log.write(json.dumps(row,sort_keys=True)+'\n');log.flush();print(name,row['status'],len(b))
