import pathlib,json,urllib.request,hashlib,datetime,sys,subprocess,resource,os
D=pathlib.Path(__file__).resolve().parents[1]
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
x=json.loads((D/'outputs/extracted.json').read_text())
for i in sys.argv[1:]:
 url=('https://api.github.com/repos/'+i.split(':',1)[1]+'/commits/HEAD') if i.startswith('registry:') else x[i]['record']['source_url'].replace('/abs/','/pdf/')
 name=i.replace(':','-').replace('/','-');receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'})
  with urllib.request.urlopen(req,timeout=15) as r: data=r.read();receipt.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  receipt['sha256']=hashlib.sha256(data).hexdigest();f=D/'sources'/ (name+('.json' if i.startswith('registry:') else '.pdf'));f.write_bytes(data)
  if not i.startswith('registry:'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=15,check=True)
 except Exception as e:receipt['error']=str(e)
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2));print(name,receipt.get('status'),receipt.get('error','OK'),flush=True)
