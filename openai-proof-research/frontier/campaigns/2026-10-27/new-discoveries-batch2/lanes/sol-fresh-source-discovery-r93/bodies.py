from pathlib import Path
import json,urllib.request,hashlib,datetime,subprocess
P=Path(__file__).parent;http=json.loads((P/'http.json').read_text());head=json.loads((P/'registries.json').read_text())['heads']['omega'];sh=json.loads((P/'sources/sepder-head.json').read_text())['sha']
paths=['Problems/separable-occupied-diagonal-lower-bound.md','Blueprint/D5/S1/Words/Patterns/Separable/OccupiedComparison.md','Blueprint/D5/S1/Words/Patterns/Separable/ActualCountRatios.md','Blueprint/D5/S1/Words/Patterns/Separable/EndpointHistoryKernel.md']
urls={f'registry-body-{i}.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+p for i,p in enumerate(paths)}
urls.update({'sepder-README.md':f'https://raw.githubusercontent.com/rdbliss/sepder/{sh}/README.md','sepder.c':f'https://raw.githubusercontent.com/rdbliss/sepder/{sh}/src/sepder.c','sepder-current.pdf':f'https://raw.githubusercontent.com/rdbliss/sepder/{sh}/paper.pdf'})
for name,url in urls.items():
 r={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read(10000000);r['status']=f.status
  (P/'sources'/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 http.append(r)
(P/'http.json').write_text(json.dumps(http,indent=2)+'\n')
