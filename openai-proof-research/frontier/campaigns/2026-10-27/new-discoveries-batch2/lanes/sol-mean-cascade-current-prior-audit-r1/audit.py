import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(35,35))
import json,hashlib,urllib.request,datetime,sys,concurrent.futures
from pathlib import Path
b=Path(__file__).resolve().parent; lanes=b.parent
D=lambda x:hashlib.sha256(x).hexdigest()
def hashes():
 out={}
 for lane in ['root-log-arctangent-formal-r1','root-cascade-formal-r1']:
  p=lanes/lane/'integrated-core-hashes.json';j=json.loads(p.read_text());a={k:{'expected':v,'actual':D((p.parent/k).read_bytes())} for k,v in j['sha256'].items()}
  out[lane]={'manifest_sha256':D(p.read_bytes()),'mathematical_modules':len(j['mathematical_modules']),'files':a,'all_match':all(v['expected']==v['actual'] for v in a.values())}
 (b/('hash-'+sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2));print({k:(v['all_match'],len(v['files'])) for k,v in out.items()})
def get(name,url):
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'bounded-primary-audit','Cache-Control':'no-cache'})
  with urllib.request.urlopen(req,timeout=20) as f:d=f.read(20000000);r.update(status=f.status,final_url=f.url,bytes=len(d),sha256=D(d),date=f.headers.get('Date'))
  (b/'sources'/name).write_bytes(d)
 except Exception as e:r['error']=str(e)
 return r
if sys.argv[1] in ['before','after']:hashes()
elif sys.argv[1]=='heads':
 tasks=[(n+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD') for n,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math'),('count','suvrit/count-ex-machina')]]
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:r=list(ex.map(lambda x:get(*x),tasks))
 (b/'http-heads.json').write_text(json.dumps(r,indent=2));print(r)
elif sys.argv[1]=='get':
 r=get(sys.argv[2],sys.argv[3]);p=b/'http-followups.json';a=json.loads(p.read_text()) if p.exists() else [];a.append(r);p.write_text(json.dumps(a,indent=2));print(r)
