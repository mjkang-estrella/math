from pathlib import Path
import urllib.request,hashlib,json,datetime
P=Path(__file__).resolve().parent;(P/'sources').mkdir(exist_ok=True)
rows=[]
for aid in ['2401.10074','2402.16259','2403.06318','2405.13618']:
 url='https://arxiv.org/html/'+aid
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requested_version='unversioned; resolved version requires body inspection')
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();row.update(status=f.status,resolved_url=f.url)
  p=P/'sources'/f'{aid}.html';p.write_bytes(b);row.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['error']=str(e)
 rows.append(row)
 (P/'source-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
