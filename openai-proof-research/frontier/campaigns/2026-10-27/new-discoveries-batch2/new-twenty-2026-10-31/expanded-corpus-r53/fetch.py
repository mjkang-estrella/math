import pathlib,urllib.request,hashlib,json,datetime,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
o=pathlib.Path(__file__).resolve().parent;(o/'sources').mkdir(exist_ok=True); receipts=[]
urls={**{a+'.pdf':'https://arxiv.org/pdf/'+a for a in ['2307.07308','2307.12458','2308.15598','2308.15303','2306.15702','2308.15588','2308.13107']},'openai-HEAD.json':'https://api.github.com/repos/openai/math/commits/HEAD','omega-HEAD.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'}
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=25) as f:data=f.read();row['status']=f.status
  (o/'sources'/name).write_bytes(data);row.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(o/'sources'/name),str(o/'sources'/name.replace('.pdf','.txt'))],capture_output=True,timeout=15)
 except Exception as e:row['error']=str(e)
 receipts.append(row);print(json.dumps(row),flush=True);(o/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
