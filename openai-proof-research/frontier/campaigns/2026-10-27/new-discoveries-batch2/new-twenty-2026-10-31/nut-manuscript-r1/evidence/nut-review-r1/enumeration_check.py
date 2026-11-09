import pathlib,re,itertools,json,resource,os,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
l=pathlib.Path(__file__).resolve().parent;f=l.parent/'nut-formal-r7q/formal';start=time.monotonic()
def tup(a):return tuple(x for r in a for x in r)
def mats(t):return [tup([[int(x) for x in r.split(',')] for r in raw.split(';')]) for raw in re.findall(r':= !!\[(.*?)\]',t)]
cert=set(a for p in f.glob('NewCertificates*.lean') for a in mats(p.read_text()))
expected=set();augmentations=0;per=[]
for file in sorted(f.glob('SupportData*.lean')):
 t=file.read_text();e=list(map(int,re.search(r'checkedEquiv \[(.*?)\]',t)[1].split(',')));p=list(map(int,re.search(r'def p .*? := !\[(.*?)\]',t)[1].split(',')));code=int(re.search(r'supportEdges (\d+)',t)[1]);edges=[(i,j) for i in range(8) for j in range(i+1,8) if code>>(i*8+j)&1];us=set();ss=set()
 for bits in itertools.product([1,2],repeat=len(edges)):
  a=[[0]*8 for _ in range(8)]
  for (i,j),w in zip(edges,bits):a[i][j]=a[j][i]=w
  rows=list(map(sum,a))
  if not all(1<=r<=3 for r in rows):continue
  for i in range(8):a[i][i]=3-rows[i]
  us.add(tup(a));u=[[a[e[i]][e[j]] for j in range(8)] for i in range(8)]
  slots=[(i,j) for i in range(8) for j in range(i,8) if (i==j and u[i][i]==2) or (i<j and p[j]!=i and u[i][j])]
  for signs in itertools.product([1,-1],repeat=len(slots)):
   for semi in [1,-1]:
    z=[r[:] for r in u]
    for i in range(8):
     if z[i][i]==1:z[i][i]=semi
    for (i,j),sign in zip(slots,signs):z[i][j]=z[j][i]=sign*u[i][j]
    ss.add(tup(z))
 stored=set(mats(t));assert us==stored,(file.name,'unsigned')
 augmentations+=len(us);expected|=ss;per.append({'support':file.stem,'unsigned':len(us),'signed':len(ss)})
assert len(per)==194 and expected==cert,(len(expected),len(cert),len(expected-cert),len(cert-expected))
(l/'enumeration-check.json').write_text(json.dumps({'supports':len(per),'unsigned_augmentations':augmentations,'signed_set_size':len(expected),'certificate_set_size':len(cert),'exact_set_equality':True,'per_support':per,'wall_seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},indent=2)+'\n')
print('PASS',len(per),augmentations,len(expected),'seconds',time.monotonic()-start)
