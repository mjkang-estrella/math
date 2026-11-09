from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, subprocess
p=Path(__file__).resolve().parent
entries=json.loads((p/'source-provenance.json').read_text()) if (p/'source-provenance.json').exists() else []
urls=[('gu','https://arxiv.org/pdf/1809.07364'),('axial','https://arxiv.org/pdf/1809.10132'),('registry-head','https://api.github.com/repos/openai/math/commits/main'),('palomar-head','https://data.palomar-registry.org/browse/index.json')]
for name,url in urls:
 try:
  with urllib.request.urlopen(url, timeout=40) as r: data=r.read(); status=r.status; final=r.url
 except urllib.error.HTTPError as e: data=e.read();status=e.code;final=e.url
 path=p/(name+('.pdf' if data[:4]==b'%PDF' else '.json'))
 path.write_bytes(data);entries.append(dict(name=name,url=url,final_url=final,status=status,date=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest(),path=str(path),bytes=len(data)))
 if data[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(path),str(p/(name+'.txt'))],check=True)
 print(name,status,len(data),flush=True)
(p/'source-provenance.json').write_text(json.dumps(entries,indent=2))
