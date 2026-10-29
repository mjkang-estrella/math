from pathlib import Path
import gzip,json,re,urllib.request,hashlib
p=Path(__file__).parent;report=json.loads((p/'current-registry.json').read_text());hits=[];count=0;tail='';pat=re.compile(r'Entropy.*Concav|Concav.*Entropy|BallNayar|Ball.Nayar|Gaussian.*Smooth|Smooth.*Gaussian|Lamkin|2609.11418|2608.00813',re.I)
with gzip.open(p/'sources/omega-current-tree.json.gz','rt') as f:
 while True:
  chunk=f.read(65536)
  if not chunk:break
  buf=tail+chunk;end=max(0,len(buf)-1000)
  for m in re.finditer(r'"path"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"',buf):
   if m.start()>=end:continue
   path=json.loads('"'+m.group(1)+'"');count+=1
   if pat.search(path):hits.append(path)
  tail=buf[end:]
 for m in re.finditer(r'"path"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"',tail):
  count+=1;path=json.loads('"'+m.group(1)+'"')
  if pat.search(path):hits.append(path)
report.update(recovered_from_saved_response=True,paths=count,truncated=bool(re.search(r'"truncated"\s*:\s*true',tail)),complete_response_tail=tail[-100:],matches=hits)
for i,path in enumerate([x for x in hits if x.endswith('.md')][:8]):
 u=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{report["head"]}/{path}'
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read(1000000)
  (p/'sources'/f'registry-body-{i}.md').write_bytes(b);report.setdefault('bodies',[]).append({'url':u,'file':f'sources/registry-body-{i}.md','sha256':hashlib.sha256(b).hexdigest()})
 except Exception as e:report.setdefault('body_errors',[]).append(str(e))
(p/'current-registry.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
