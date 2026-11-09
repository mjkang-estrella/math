import pathlib,json,urllib.request,datetime,hashlib,resource,concurrent.futures,subprocess,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
D=json.loads((L/'literal-records.json').read_text())
jobs=[(u.rsplit('/',1)[-1]+sfx,'https://arxiv.org/'+route+'/'+u.rsplit('/',1)[-1]) for u in sorted({x['record']['source_url'] for x in D.values()}) for sfx,route in [('.abs.html','abs'),('.pdf','pdf')]]
def fetch(job):
 name,url=job;t=datetime.datetime.now(datetime.timezone.utc).isoformat();r={'url':url,'utc':t}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=15) as f:b=f.read(18000000);r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/name).write_bytes(b)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/name),str(L/name.replace('.pdf','.txt'))],timeout=15,check=False)
 except Exception as e:r['error']=str(e)
 (L/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));return name,r.get('status'),r.get('error')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs): print(r,flush=True)
