from pathlib import Path
import urllib.request,json,hashlib,datetime,sys
R=Path(__file__).resolve().parent;(R/'primary').mkdir(exist_ok=True)
urls={
'heisenberg':'https://web.math.princeton.edu/~aizenman/OpenProblems_MathPhys/9901.HeisenbergFerr.html',
'fermi':'https://web.math.princeton.edu/~aizenman/OpenProblems_MathPhys/9807.FermiGas.html',
'bose':'https://web.math.princeton.edu/~aizenman/OpenProblems_MathPhys/9801.BEcond.html',
'simon':'https://en.wikipedia.org/w/index.php?title=Simon_problems&oldid=1335881350',
'quantum':'https://arxiv.org/pdf/2002.03233',
'mccurley':'https://mccurley.org/papers/open.ps.gz',
'dtuples':'https://web.math.pmf.unizg.hr/~duje/dtuples.html',
'complexity':'https://arxiv.org/pdf/math/0312440',
'ipam':'https://www.ipam.ucla.edu/programs/workshops/workshop-i-number-theory-and-cryptography-open-problems/?tab=schedule'}
if len(sys.argv)>1:urls=json.loads(sys.argv[2]) if sys.argv[1]=='--list' else {sys.argv[1]:sys.argv[2]}
for name,url in urls.items():
 meta={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'URL as supplied; response headers retained','status':'not_requested'}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'})
  with urllib.request.urlopen(req,timeout=25) as f:
   meta.update(status=f.status,final_url=f.url,headers=dict(f.headers));data=f.read(12*1024*1024+1)
   assert len(data)<=12*1024*1024,'download cap'
  meta.update(sha256=hashlib.sha256(data).hexdigest(),size=len(data));(R/'primary'/name).write_bytes(data)
 except Exception as e:meta.update(error=repr(e))
 (R/'primary'/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n');print(name,meta['status'],meta.get('size'),meta.get('error'))
