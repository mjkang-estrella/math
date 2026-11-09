from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
r=json.loads((L/'records.json').read_text());jobs=[]
for x in r.values():
 x['statement_sha256']=hashlib.sha256(x['record']['statement'].encode()).hexdigest()
 s=x['record']['source_url'].split('/abs/')[-1]
 for name,url in [(s+'-abs.html','https://arxiv.org/abs/'+s),(s+'.pdf','https://arxiv.org/pdf/'+s)]:
  if [name,url] not in jobs:jobs.append([name,url])
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 jobs.extend([[name+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD'],[name+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/HEAD?recursive=1']])
jobs.append(['projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml'])
(L/'fetch-plan.json').write_text(json.dumps(jobs));(L/'records.json').write_text(json.dumps(r,indent=2,ensure_ascii=False))
