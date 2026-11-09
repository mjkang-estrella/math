import pathlib,json,hashlib,urllib.request,datetime,resource,concurrent.futures,re,subprocess,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
r=pathlib.Path(__file__).resolve().parent; (r/'sources').mkdir(exist_ok=True)
rows=json.loads((r/'reservation.json').read_text())['rows']
receipts=[]
def get(job):
 name,url=job; dest=r/'sources'/name; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(dest.relative_to(r))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review (public read-only)'}),timeout=12) as res:
   data=res.read(15*1024**2);rec.update(status=res.status,final_url=res.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));dest.write_bytes(data)
  if data.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],timeout=15,check=True,capture_output=True)
 except Exception as e:rec['error']=str(e)
 return rec
mode=sys.argv[1] if len(sys.argv)>1 else 'abs'
if mode=='abs': jobs=[(str(x['mathdb_id'])+'.abs.html',x['source_url']) for x in rows]
elif mode=='pdf':
 jobs=[]
 for x in rows:
  p=r/'sources'/(str(x['mathdb_id'])+'.abs.html'); s=p.read_text(errors='replace') if p.exists() else ''
  versions=sorted(set(re.findall(r'\['+r'v(\d+)\]',s)),key=int) or ['1']
  for v in versions: jobs.append((str(x['mathdb_id'])+'v'+v+'.pdf','https://arxiv.org/pdf/'+x['source_url'].split('/')[-1]+'v'+v))
else: raise ValueError(mode)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(get,jobs):
  receipts.append(rec); print(json.dumps(rec),flush=True)
(r/('receipts-'+mode+'.json')).write_text(json.dumps(receipts,indent=2)+'\n')
