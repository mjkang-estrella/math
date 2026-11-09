import urllib.request,urllib.error,json,hashlib,datetime,pathlib,sys
L=pathlib.Path(__file__).resolve().parent
queries=[('arxiv-abs','https://arxiv.org/abs/1803.00823'),('crossref','https://api.crossref.org/works?query.title=The%20No%20Justice%20in%20the%20Universe%20phenomenon&rows=3'),('arxiv-prior','https://export.arxiv.org/api/query?search_query=all:%22honest%20tournaments%22&start=0&max_results=20')]
if len(sys.argv)>1:queries=[(sys.argv[1],sys.argv[2])]
for name,url in queries:
 row={'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalSourceReview/1.0'}),timeout=25) as r:
   data=r.read(2000000);row.update(status=r.status,final_url=r.url)
  p=L/'current'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data)
  row.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:row.update(error=str(e))
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row))
