import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,re,json,urllib.request,datetime,time,hashlib
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic();rs=[]
for name,url in [('pool-candidates-pinned','https://raw.githubusercontent.com/LeanPool/lean-pool/882795354c57bfed5c5fbbf950aa8ff840f4ff17/candidates/README.md'),('pool-import-pinned','https://raw.githubusercontent.com/LeanPool/lean-pool/882795354c57bfed5c5fbbf950aa8ff840f4ff17/LeanPool.lean'),('pool-readme-pinned','https://raw.githubusercontent.com/LeanPool/lean-pool/882795354c57bfed5c5fbbf950aa8ff840f4ff17/README.md')]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'routing index only'}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read(5*1024**2);r.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file='sources/'+name+'.txt');(L/r['file']).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 rs.append(r)
(L/'http-receipts-registry.json').write_text(json.dumps(rs,indent=2)+'\n')
for i in [357256,357736,357935,363952,365524]:
 txt=(L/f'text/{i}-html.txt').read_text();print('DEFS',i)
 for term in {357256:['positive definite','Definition.'],357736:['Definition 2.1','linear transformations'],357935:['Definition 4.1'],363952:['Conjecture 1.1'],365524:['Theorem 1.8']}[i]:
  m=re.search(re.escape(term),txt,re.I);print(txt[max(0,m.start()-200):m.start()+1000] if m else 'not found')
txt=(L/'text/358287-html.txt').read_text()
for term in ['Conjecture 5.9','Conjecture 5.10','two rows','length 2']:
 m=re.search(term,txt,re.I)
 if m:print('KRON',txt[max(0,m.start()-150):m.start()+1200])
print('REGISTRY',rs)
(L/'resource-final-reads.json').write_text(json.dumps({'exit':0,'wall':time.monotonic()-t,'self':list(resource.getrusage(resource.RUSAGE_SELF)),'all_fetches_closed':True})+'\n')
