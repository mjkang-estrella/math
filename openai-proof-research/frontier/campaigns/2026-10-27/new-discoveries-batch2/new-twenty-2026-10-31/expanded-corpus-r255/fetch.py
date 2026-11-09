import pathlib,json,urllib.request,urllib.error,hashlib,datetime,concurrent.futures,resource,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent
jobs=json.loads((L/sys.argv[1]).read_text())
def run(j):
 name,url=j; t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=18) as r: b=r.read(25000000);s=r.status
 except urllib.error.HTTPError as e:s=e.code;b=e.read()
 except Exception as e:s=str(e);b=b''
 (L/(name+'.body')).write_bytes(b)
 d={'url':url,'utc':t,'status':s,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
 (L/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return [name,s,len(b)]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for d in ex.map(run,jobs): print(d,flush=True)
