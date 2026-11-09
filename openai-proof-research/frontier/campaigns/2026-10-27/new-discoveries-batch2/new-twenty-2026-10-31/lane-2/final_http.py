import requests,pathlib,hashlib,json,datetime,subprocess,concurrent.futures
p=pathlib.Path('.')
rows=json.load(open('../../lanes/sol-mathdb-primary-qualified-breadth-r728/literal-records.json'))
urls={'janson':'https://combinatorialpress.com/article/ojac/vol8/74.pdf','proofsearch':'https://proofsearch.org/','prove2me':'https://prove2.me/'}
for x in rows:
 r=x['record'];i=r['mathdb_id']
 if i in [319825,320868,321049]:urls['mathdb-'+str(i)]=r['canonical_url']
def get(k,u):
 try:
  r=requests.get(u,timeout=30);ext='pdf' if r.content.startswith(b'%PDF') else 'txt';f=p/(k+'.'+ext);f.write_bytes(r.content)
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(p/(k+'.txt'))],check=True)
  return dict(name=k,url=u,status=r.status_code,file=str(f),sha256=hashlib.sha256(r.content).hexdigest(),date=datetime.datetime.now(datetime.timezone.utc).isoformat(),headers=dict(r.headers))
 except Exception as e:return dict(name=k,url=u,error=str(e))
log=json.load(open('http-manifest.json'));log.append(dict(name='janson-first-attempt',url='https://www2.math.uu.se/~svantejs/papers/sj280.pdf',error='SSL certificate verification failed; no verification bypass',date=datetime.datetime.now(datetime.timezone.utc).isoformat()));new=list(concurrent.futures.ThreadPoolExecutor(6).map(lambda x:get(*x),urls.items()));log+=new;(p/'http-manifest.json').write_text(json.dumps(log,indent=2));print([{k:v for k,v in x.items() if k!='headers'} for x in new])
