from pathlib import Path
import urllib.request,json,hashlib,datetime
p=Path(__file__).resolve().parent;head=json.loads((p/'live/omega-head.json').read_text())['sha']; base='556e7696bbabaff203d45456d177c5ce5b714212'
urls={'omega-new-delta.json':f'https://api.github.com/repos/the-omega-institute/trureturing/compare/{base}...{head}','omega-current-blueprint.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/Blueprint/D5/S1/Recurrence/MatveevaGlobalBoundedness.md','omega-current-endpoint.lean':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/D5/S1/Recurrence/MatveevaGlobalBoundedness.lean'}
rows=[]
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read();row['status']=f.status
  (p/'live'/name).write_bytes(data);row['sha256']=hashlib.sha256(data).hexdigest();row['file']='live/'+name
  if name.endswith('.json'):
   j=json.loads(data);print('delta',j.get('total_commits'),[f['filename'] for f in j.get('files',[])])
  else:print(name,row['sha256'])
 except Exception as e:row['error']=str(e)
 rows.append(row)
(p/'delta-http.json').write_text(json.dumps(rows,indent=2))
