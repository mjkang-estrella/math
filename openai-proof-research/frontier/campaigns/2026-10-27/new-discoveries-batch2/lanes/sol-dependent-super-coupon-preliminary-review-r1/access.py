from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime
L=Path(__file__).resolve().parent
rows=[]
urls=[('target-current','https://arxiv.org/abs/2304.01145'),('bounded-search','https://arxiv.org/search/?query=%22coupon+collector%22+Markov&searchtype=all&abstracts=show&order=-announced_date_first&size=50')]
for name,url in urls:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retries':0}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'}),timeout=25) as f:
   row['status']=f.status;row['resolved_url']=f.url;data=f.read(2000001)
  if len(data)>2000000:raise ValueError('bounded body exceeded 2MB')
  p=L/'retrieved'/f'{name}.html';p.parent.mkdir(exist_ok=True);p.write_bytes(data)
  h=hashlib.sha256(data).hexdigest();q=L/'frozen'/'live'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(data)
  assert h==hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()
  row.update(original=str(p),copy=str(q),sha256=h,bytes=len(data))
 except Exception as e:row['failure']=str(e)
 rows.append(row)
 if row.get('status') in [403,429] or '403' in row.get('failure','') or '429' in row.get('failure',''):break
(L/'access.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
