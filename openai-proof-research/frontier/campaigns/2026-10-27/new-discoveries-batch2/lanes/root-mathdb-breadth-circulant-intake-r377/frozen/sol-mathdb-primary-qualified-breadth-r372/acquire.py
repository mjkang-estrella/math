from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,re
L=Path(__file__).parent;(L/'sources').mkdir(exist_ok=True)
jobs=[('cover-shift-original','https://ems.press/journals/owr/articles/11136'),('toric-original','https://ems.press/journals/owr/articles/4527'),('simplex-original','https://ems.press/journals/owr/articles/4136'),('polygon-original','https://ems.press/journals/owr/articles/13110'),('shift-successor','https://arxiv.org/pdf/2609.31549v1'),('polygon-successor','https://arxiv.org/pdf/1412.0371v1')]
rows=[]
for name,url in jobs:
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source audit/1.0'}),timeout=22) as r: b=r.read(16000000);row.update(status=r.status,final_url=r.url)
  row.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));p=L/'sources'/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);row['path']=str(p)
  # bind before any semantic processing
  rows.append(row);(L/'sources.json').write_text(json.dumps(rows,indent=2)+'\n')
  challenge=any(x in b[:100000].lower() for x in [b'cf-chl-',b'proof-of-work',b'just a moment',b'verify you are human',b'captcha'])
  row['challenge']=challenge
  if not challenge and p.suffix=='.html':print(name, re.findall(r'[^"\s<>]+\.pdf[^"\s<>]*',b.decode(errors='replace'))[:12])
 except Exception as e:row['failure']=str(e);rows.append(row)
 (L/'sources.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(name,row.get('status'),row.get('failure'),row.get('challenge'))
