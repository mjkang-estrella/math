import pathlib,itertools,json,subprocess,runpy
D=pathlib.Path(__file__).resolve().parents[1];S='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';out=[]
# Reuse verified incidence data; no execution/import of downloaded code.
planes={r['q']:r for r in json.loads((D/'outputs/percolation.json').read_text())}
for q,r in [(4,4),(5,5),(7,5),(7,6),(7,7)]:
 data=planes[q];N=len(data['plane_points']);lines=[[p for p in range(N) if l>>p&1] for l in data['lines']];A=lambda p:p+1;P=lambda p:N+p+1;I=lambda l:2*N+l+1;J=lambda l:3*N+l+1;B=lambda v,p:4*N+v*N+p+1;cl=[]
 for l,pts in enumerate(lines):
  for sub in itertools.combinations(pts,len(pts)-r+1):
   cl.append([-I(l)]+[A(p) for p in sub]);cl.append([-J(l)]+[P(p) for p in sub])
 for p in range(N):
  inc=[l for l,pts in enumerate(lines) if p in pts]
  cl.append([-P(p),A(p)]+[I(l) for l in inc]);cl.append([-A(p),P(p)])
  for l in inc:cl.append([-I(l),P(p)])
  cl.append([P(p)]+[J(l) for l in inc])
 cl.append([-P(p) for p in range(N)])
 for v in range(N):
  cl.append([-A(v),-B(v,v)])
  for p in range(N):
   if p!=v:cl.append([-A(v),-A(p),B(v,p)])
  for pts in lines:
   for sub in itertools.combinations(pts,r):
    for p in pts:
     if p not in sub:cl.append([-B(v,u) for u in sub]+[B(v,p)])
 p=D/'outputs'/('percolation-%d-%d.cnf'%(q,r));p.write_text('p cnf %d %d\n'%(4*N+N*N,len(cl))+''.join(' '.join(map(str,c))+' 0\n' for c in cl))
 z=subprocess.run([S,'-q','-t','15',str(p)],capture_output=True,text=True);(D/'logs'/('percolation-sat-%d-%d.log'%(q,r))).write_text(z.stdout);rec={'q':q,'r':r,'returncode':z.returncode,'variables':4*N+N*N,'clauses':len(cl)}
 if z.returncode==10:
  pos={int(x) for l in z.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0};assert all(any((x>0 and x in pos) or (x<0 and -x not in pos) for x in c) for c in cl)
  mask=sum(1<<p for p in range(N) if A(p) in pos);L=data['lines'];full=(1<<N)-1
  def step(a):
   b=a
   for l in L:
    if (a&l).bit_count()>=r:b|=l
   return b
  def closure(a):
   while 1:
    b=step(a)
    if b==a:return a
    a=b
  assert step(mask)!=full and step(step(mask))==full
  assert all(closure(mask&~(1<<p))!=full for p in range(N) if mask>>p&1)
  rec['mask']=mask;rec['points']=[data['plane_points'][p] for p in range(N) if mask>>p&1]
 out.append(rec);(D/'outputs/percolation-sat.json').write_text(json.dumps(out));print(rec,flush=True)
