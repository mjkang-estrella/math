from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,subprocess
p=Path(__file__).resolve().parent;e=json.loads((p/'source-provenance.json').read_text());head=json.loads((p/'registry-head.json').read_text())['sha']
urls=[('registry-contents',f'https://raw.githubusercontent.com/openai/math/{head}/CONTENTS.md'),('palomar-anchored','https://data.palomar-registry.org/api/v1/results?q=anchored'),('palomar-sidon','https://data.palomar-registry.org/api/v1/results?q=Sidon'),('palomar-axial','https://data.palomar-registry.org/api/v1/results?q=axial'),('axial-2026','https://arxiv.org/pdf/2606.30048')]
for name,url in urls:
 try:
  with urllib.request.urlopen(url,timeout=35) as r:data=r.read();status=r.status;final=r.url
 except urllib.error.HTTPError as r:data=r.read();status=r.code;final=r.url
 f=p/(name+('.pdf' if data[:4]==b'%PDF' else '.body'));f.write_bytes(data)
 e.append(dict(name=name,url=url,status=status,final_url=final,date=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(f)))
 if data[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(f),str(p/(name+'.txt'))],check=True)
 print(name,status,len(data),flush=True)
(p/'source-provenance.json').write_text(json.dumps(e,indent=2))
