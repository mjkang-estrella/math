from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
R=Path(__file__).resolve().parent
url='https://wrap.warwick.ac.uk/id/eprint/170329/1/WRAP-Haystack-hunting-hints-and-locker-room-communication-Kontogeogiou-2022.pdf'
e={'key':'347713-published','url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=15) as f: data=f.read(10000000);e['final_url']=f.url
 assert data.startswith(b'%PDF')
 p=R/'sources/347713-published.pdf';p.write_bytes(data)
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
 e.update(status='retained',sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
except Exception as ex:e.update(status='failure',error=str(ex))
(R/'published-provenance.json').write_text(json.dumps(e,indent=2)+'\n');print(e['status'])
