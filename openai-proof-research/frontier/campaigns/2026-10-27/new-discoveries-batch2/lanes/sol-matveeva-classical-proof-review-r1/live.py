from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
p=Path(__file__).resolve().parent
head='556e7696bbabaff203d45456d177c5ce5b714212'
urls={'latest-abs.html':'https://arxiv.org/abs/2511.02121','latest-source.html':'https://arxiv.org/html/2511.02121v1','omega-blueprint.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S1/Recurrence/MatveevaGlobalBoundedness.md','omega-endpoint.lean':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/D5/S1/Recurrence/MatveevaGlobalBoundedness.lean'}
r=[]
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read();row['status']=f.status
  (p/'live').mkdir(exist_ok=True);(p/'live'/name).write_bytes(data);row.update(file='live/'+name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e: row['error']=str(e)
 r.append(row)
(p/'live-http.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
