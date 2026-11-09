import pathlib,json,hashlib,datetime,resource,os,concurrent.futures,urllib.request,subprocess,re,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3)); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent; (p/'sources').mkdir(exist_ok=True)
r=json.loads((p/'literal-records.json').read_text()); ids=sorted(set(v['record']['source_url'].split('/')[-1] for v in r.values())); phase=__import__('sys').argv[1] if len(__import__('sys').argv)>1 else 'base'
jobs=[]
if phase=='base':
 for a in ids: jobs += [(f'{a}.abs.html',f'https://arxiv.org/abs/{a}'),(f'{a}.pdf',f'https://arxiv.org/pdf/{a}')]
elif phase=='versions':
 for a in ids:
  f=p/'sources'/f'{a}.abs.html'
  if f.exists():
   for v in sorted(set(re.findall(r'\[v(\d+)\]',f.read_text())),key=int): jobs.append((f'{a}v{v}.pdf',f'https://arxiv.org/pdf/{a}v{v}'))
else:
 jobs=json.loads((p/phase).read_text())
def fetch(j):
 name,url=j; t=time.monotonic(); o={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=7) as a: b=a.read(20000000); o.update(status=a.status,final_url=a.url)
  (p/'sources'/name).write_bytes(b); o.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],timeout=8,check=True,capture_output=True)
 except Exception as e: o['error']=str(e)
 o['wall_seconds']=round(time.monotonic()-t,2); return o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
 for o in e.map(fetch,jobs):
  with (p/'fetch-receipts.jsonl').open('a') as f:f.write(json.dumps(o)+'\n')
  print(o['name'],o.get('status',o.get('error')),flush=True)
print('usage',resource.getrusage(resource.RUSAGE_SELF),flush=True)
