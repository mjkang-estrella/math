from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime
L=Path(__file__).parent
queries=[('current','https://arxiv.org/abs/2007.12338'),('later','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"quantile mixture"')+'&start=0&max_results=30'),('companion','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"aggregation sets"')+'&start=0&max_results=30')]
for name,url in queries:
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=30) as r:
   data=r.read(4000000);row['status']=r.status
  dst=L/'sources'/name;dst.parent.mkdir(exist_ok=True);dst.write_bytes(data);dst.chmod(0o444)
  row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(dst.relative_to(L)))
 except Exception as e:row['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(row)
