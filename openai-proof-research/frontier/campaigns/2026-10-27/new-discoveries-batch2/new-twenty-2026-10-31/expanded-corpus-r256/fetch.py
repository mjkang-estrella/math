import sys,pathlib,json,hashlib,datetime,urllib.request,urllib.error,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent

def fetch(pair):
 name,url=pair; t=datetime.datetime.now(datetime.timezone.utc).isoformat(); r={'url':url,'utc':t,'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=20) as f:b=f.read(25*1024**2);r.update(status=f.status,final_url=f.url)
  (L/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r.update(status=getattr(e,'code',None),error=str(e))
 (L/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
if __name__=='__main__':
 jobs=json.loads(pathlib.Path(sys.argv[1]).read_text())
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(fetch,jobs))
