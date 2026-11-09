from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
p=Path(__file__).resolve().parent
sources=[('later-greedy.pdf','https://drops.dagstuhl.de/storage/00lipics/lipics-vol198-icalp2021/LIPIcs.ICALP.2021.61/LIPIcs.ICALP.2021.61.pdf'),('balas-toth.pdf','https://csun.edu/~ctoth/Manuscripts/anchored-enum.pdf'),('registry-head.json','https://api.github.com/repos/openai/math/commits/main'),('palomar-index.body','https://data.palomar-registry.org/browse/index.json')]
rows=[]
for name,url in sources:
 row=dict(url=url,date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch source-check'}),timeout=25) as r: data=r.read();row.update(status=r.status,final_url=r.url)
 except urllib.error.HTTPError as e: data=e.read();row.update(status=e.code,error=str(e))
 except Exception as e: data=b'';row.update(error=str(e))
 (p/name).write_bytes(data);row.update(file=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());rows.append(row);print(json.dumps(row),flush=True)
 if name=='registry-head.json' and row.get('status')==200:
  d=json.loads(data); sha=d['sha']; u=f'https://raw.githubusercontent.com/openai/math/{sha}/CONTENTS.md'
  try:
   with urllib.request.urlopen(u,timeout=25) as r: b=r.read()
   (p/'registry-CONTENTS.md').write_bytes(b); rows.append(dict(url=u,status=200,date_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(b).hexdigest(),file='registry-CONTENTS.md',bytes=len(b),commit=sha,commit_date=d['commit']['committer']['date']))
  except Exception as e: rows.append(dict(url=u,error=str(e)))
(p/'source-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
