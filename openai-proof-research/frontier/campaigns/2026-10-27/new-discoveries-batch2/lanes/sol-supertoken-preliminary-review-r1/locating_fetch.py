from review_tools import *
import urllib.request,urllib.error,subprocess
u='https://arxiv.org/pdf/1506.02623';stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
 with urllib.request.urlopen(u,timeout=30) as f:raw=f.read(8000000);status=f.status
 (R/'locating.pdf').write_bytes(raw);rec=dict(url=u,utc=stamp,status=status,path='locating.pdf',sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
except urllib.error.HTTPError as e:rec=dict(url=u,utc=stamp,status=e.code,error=str(e));raw=None
with (R/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(json.dumps(rec))
if raw:
 subprocess.run(['pdftotext','-layout',str(R/'locating.pdf'),str(R/'locating.txt')],check=True)
 print((R/'locating.txt').read_text()[:14500])
