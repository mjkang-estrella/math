from pathlib import Path
import urllib.request,hashlib,json,datetime
r=Path(__file__).resolve().parent
base='https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/'
urls={'coprime-claim.md':base+'Problems/coprime-divisor-tuples.md','coprime-proof.lean':base+'D5/S3/Arith/CoprimeDivisorTuples.lean'}
rows=[]
for name,url in urls.items():
 d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:v=f.read();d['status']=f.status
  (r/d['file']).write_bytes(v);d['sha256']=hashlib.sha256(v).hexdigest()
 except Exception as e:d['error']=repr(e)
 rows.append(d)
(r/'sources/fetch-claims.json').write_text(json.dumps(rows,indent=2))
