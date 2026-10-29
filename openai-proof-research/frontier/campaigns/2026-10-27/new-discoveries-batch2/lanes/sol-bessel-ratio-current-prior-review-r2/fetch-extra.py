from pathlib import Path
import urllib.request,datetime,hashlib,json,subprocess
out=Path(__file__).parent;url='https://arxiv.org/pdf/2604.04844v1';rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
try:
 with urllib.request.urlopen(url,timeout=25) as r:
  data=r.read(12000000);(out/'public/contest.pdf').write_bytes(data);rec.update(status=r.status,headers=dict(r.headers),file='public/contest.pdf',sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 subprocess.run(['pdftotext','-layout',str(out/'public/contest.pdf'),str(out/'public/contest.txt')],check=True,timeout=20)
except Exception as e:rec['error']=str(e)
with (out/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(rec.get('status',rec.get('error')))
