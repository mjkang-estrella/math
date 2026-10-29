from pathlib import Path
import json,urllib.request,re,gzip,hashlib,datetime
p=Path(__file__).parent;head=json.loads((p/'sources/omega-head.json').read_text());sha=head['sha'];tree=head['commit']['tree']['sha']
url=f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{tree}?recursive=1';hits=[];count=0;truncated=None;pat=re.compile(r'Entropy.*Concav|Concav.*Entropy|BallNayar|Ball.Nayar|Gaussian.*Smooth|Smooth.*Gaussian|Lamkin|2609.11418|2608.00813',re.I)
report={'url':url,'head':sha,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=30) as r,gzip.open(p/'sources/omega-current-tree.json.gz','wb') as out:
  for line in r:
   out.write(line)
   if b'"path":' in line:
    path=json.loads(line.decode().strip().split(':',1)[1].rstrip(','));count+=1
    if pat.search(path):hits.append(path)
   if b'"truncated":' in line:truncated=b'true' in line
 report.update(paths=count,truncated=truncated,matches=hits)
except Exception as e:report['error']=str(e)
for i,path in enumerate([x for x in hits if x.endswith('.md')][:8]):
 u=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/{path}'
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read(1000000)
  (p/'sources'/f'registry-body-{i}.md').write_bytes(b)
  report.setdefault('bodies',[]).append({'path':path,'url':u,'file':f'sources/registry-body-{i}.md','sha256':hashlib.sha256(b).hexdigest()})
 except Exception as e:report.setdefault('failures',[]).append({'url':u,'error':str(e)})
(p/'current-registry.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
