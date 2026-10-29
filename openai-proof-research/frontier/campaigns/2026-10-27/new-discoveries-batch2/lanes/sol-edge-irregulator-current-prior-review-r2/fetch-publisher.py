from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess
P=Path(__file__).resolve().parent;url='https://link.springer.com/content/pdf/10.1007/978-981-95-7127-7_24.pdf?pdf=inline%20link';row={'url':url,'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=22) as r:data=r.read();row.update(status=r.status,final_url=r.url,headers=dict(r.headers))
except urllib.error.HTTPError as e:data=e.read();row.update(status=e.code,error=str(e))
except Exception as e:data=b'';row['error']=repr(e)
f=P/'live/publisher.pdf';f.write_bytes(data);row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat())
if data.startswith(b'%PDF'):row['pdftotext_exit']=subprocess.run(['pdftotext','-layout',str(f),str(P/'live/publisher-pdf.txt')]).returncode
(P/'live/publisher-pdf-http.json').write_text(json.dumps(row,indent=2));print(row)
