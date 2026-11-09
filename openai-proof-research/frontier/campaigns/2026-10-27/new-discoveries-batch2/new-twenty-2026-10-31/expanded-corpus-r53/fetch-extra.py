import pathlib,urllib.request,datetime,hashlib,json,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
o=pathlib.Path(__file__).resolve().parent;r=[]
for name,url in [('supernorm-published.html','https://link.springer.com/article/10.1007/s11139-024-00893-8'),('graph-author-version.pdf','https://www.mathstat.dal.ca/~tkolokol/maxgraphs/paper.pdf')]:
 row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read();row['status']=f.status
  (o/'sources'/name).write_bytes(data);row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.endswith('pdf'):subprocess.run(['pdftotext','-layout',str(o/'sources'/name),str(o/'sources'/name.replace('.pdf','.txt'))],capture_output=True,timeout=20)
 except Exception as e:row['error']=str(e)
 r.append(row);print(json.dumps(row),flush=True)
(o/'extra-source-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
