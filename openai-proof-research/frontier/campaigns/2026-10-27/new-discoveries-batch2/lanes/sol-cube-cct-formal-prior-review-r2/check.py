import pathlib,hashlib,json,shutil,collections,tarfile,gzip,io
L=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
P=L.parent/'sol-cube-cct-preliminary-review-r1/primary'
records=json.loads((L/'freeze.json').read_text())
for n in ['published.pdf','published.txt','published.pdf.receipt.json','published.extract.json','kocay.txt','geometry.txt','chains.txt','arxiv-prior.xml']:
 p=P/n;q=L/'frozen/primary'/n;q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);shutil.copyfile(p,q);assert h==sha(p)==sha(q)
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'freeze.json').write_text(json.dumps(records,indent=2))
# Explicit tuples, independently count all 1024 ordered pairs, rather than assuming 2^distance.
points=[tuple(-1 if (v>>i)&1 else 1 for i in range(5)) for v in range(32)]
assert len(set(points))==32
fib=collections.Counter(tuple(a+b for a,b in zip(x,y)) for x in points for y in points)
Z=[2,9,10,13,19,20];X=set(Z)-{9};Y=set(Z)-{2}
w=lambda a,b:fib[tuple(x+y for x,y in zip(points[a],points[b]))]
table=[[w(a,b) for b in Z] for a in Z];scores=list(map(sum,table))
assert scores==[39,39,39,51,45,57] and w(9,13)==2 and w(2,13)==16
def A(x):return (-x[0],x[4],x[3],x[1],x[2])
def B(x):return (-x[0],x[3],x[4],x[2],x[1])
assert all(B(A(x))==x==A(B(x)) for x in points)
g=[points.index(A(x)) for x in points];assert len(set(g))==32 and {g[x] for x in X}==Y
assert all(w(g[a],g[b])==w(a,b) for a in range(32) for b in range(32))
(L/'independent-math.json').write_text(json.dumps(dict(universe_size=len(points),ordered_pairs=sum(fib.values()),Z=Z,weights=table,scores=scores,g=g,images_X={str(x):g[x] for x in sorted(X)},inverse_verified=True),indent=2))
# Rebuild original packaging byte-identically from extracted immutable members.
buf=io.BytesIO()
with gzip.GzipFile(filename='',mode='wb',fileobj=buf,mtime=0) as gz:
 with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as t:
  for p in sorted((L/'replay').iterdir()):
   if p.name not in json.loads((L/'replay/source-manifest.json').read_text()) and p.name!='source-manifest.json':continue
   data=p.read_bytes();i=tarfile.TarInfo(p.name);i.size=len(data);i.mode=0o644;i.uid=i.gid=i.mtime=0;i.uname=i.gname='';t.addfile(i,io.BytesIO(data))
h=hashlib.sha256(buf.getvalue()).hexdigest();assert h==sha(L/'frozen/source/source-only.tar.gz')
(L/'archive-rebuild.json').write_text(json.dumps(dict(sha256=h,byte_identical=True,own_oleans_in_archive=False),indent=2))
print('independent counts, inverse, transport and deterministic rebuild PASS')
