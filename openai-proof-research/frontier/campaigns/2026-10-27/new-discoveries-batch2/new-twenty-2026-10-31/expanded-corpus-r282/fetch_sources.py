import resource, pathlib,json,datetime,hashlib,concurrent.futures,urllib.request,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
raw=json.loads((p/'raw-records.json').read_text()); jobs={}
for k,v in raw.items():
 r=v['record'];u=r['source_url']
 if 'arxiv.org/abs/' in u:
  a=u.split('/abs/')[1];jobs[a.replace('/','_')+'.abs.html']=u;jobs[a.replace('/','_')+'.pdf']='https://arxiv.org/pdf/'+a
 elif 'egres' in u: jobs[k+'.html']=r.get('first_stated_year_source_url') if 'lemon' in r.get('first_stated_year_source_url','') else u
 elif 'topp.' in u: jobs[k+'.html']=u
 else: jobs['stflour.pdf']='https://www.wisdom.weizmann.ac.il/~itai/stflouraug24.pdf'
def one(it):
 name,u=it;t=time.monotonic();d={'file':name,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-review/1.0'}),timeout=18) as r:b=r.read(16000000);d.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(s/name).write_bytes(b)
 except Exception as e:d['error']=str(e)
 d['wall_seconds']=time.monotonic()-t;(s/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return d
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
 for x in pool.map(one,jobs.items()): print(json.dumps(x),flush=True)
