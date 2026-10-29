import urllib.request,hashlib,json,datetime,pathlib,sys
P=pathlib.Path(__file__).resolve().parent
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=35) as r:
   data=r.read(12000000);row.update(status=r.status,content_type=r.headers.get('Content-Type'),final_url=r.url)
  if name.endswith('.pdf') and not data.startswith(b'%PDF'):raise ValueError('not PDF bytes')
  (P/'sources'/name).write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:row['error']=str(e)
 with (P/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row))
