from pathlib import Path
import urllib.request,json,hashlib,subprocess
P=Path(__file__).resolve().parent;log=json.loads((P/'http.json').read_text())
urls={'melonic_vor.pdf':'https://ems.press/content/serial-article-files/39475','chen_vor':'https://www.sciencedirect.com/science/article/pii/S0393044025002517','gamma_vor':'https://www.ams.org/journals/proc/2026-154-02/S0002-9939-2025-17396-7/S0002-9939-2025-17396-7.pdf'}
for name,url in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit'}),timeout=25) as r:b=r.read();status=r.status
  f=P/'sources'/name;f.write_bytes(b);log.append(dict(name=name,url=url,status=status,file=str(f.relative_to(P)),sha256=hashlib.sha256(b).hexdigest()))
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],check=True)
 except Exception as e:log.append(dict(name=name,url=url,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2));print(log[-3:])
# Current delta bodies: read every changed file, not absence of candidate words in names
head=json.loads((P/'sources/omega_head.json').read_text())['sha']
for i,r in enumerate(json.loads((P/'sources/omega_delta.json').read_text()).get('files',[])):
 url='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+r['filename']
 try:
  with urllib.request.urlopen(url,timeout=20) as response:b=response.read()
  f=P/'sources'/('omega-delta-body-'+str(i)+'.md');f.write_bytes(b);log.append(dict(url=url,status=200,file=str(f.relative_to(P)),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:log.append(dict(url=url,error=str(e)))
(P/'http.json').write_text(json.dumps(log,indent=2))
