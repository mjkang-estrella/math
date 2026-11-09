import pathlib,urllib.request,urllib.error,hashlib,json,datetime,resource,sys
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
D=pathlib.Path(__file__).resolve().parent; (D/'sources').mkdir(exist_ok=True)
urls={
'github-head':'https://api.github.com/repos/openai/math/commits/main',
'aim-fourier':'https://aimpl.org/fourierconvex/1/',
'sticky':'https://pmc.ncbi.nlm.nih.gov/articles/PMC6405455/',
'slab-tail':'https://www.math.cmu.edu/~ttkocz/mypapers/mathematics/unif-gauss-tail.pdf',
}
if len(sys.argv)>1: urls=json.loads(sys.argv[1])
for name,url in urls.items():
 r={'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25) as f:
   data=f.read(16000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers),sha256=hashlib.sha256(data).hexdigest(),size=len(data));(D/'sources'/name).write_bytes(data)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 r['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(D/'sources'/f'{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(name,r.get('status'),r.get('sha256'),r.get('error'))
