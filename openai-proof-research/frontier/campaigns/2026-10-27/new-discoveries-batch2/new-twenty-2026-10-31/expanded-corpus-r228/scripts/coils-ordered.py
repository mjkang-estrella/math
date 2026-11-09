import itertools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
def topo(vs,edges):
 out=[]
 def rec(done):
  if len(done)==len(vs):out.append(done);return
  for v in vs:
   if v not in done and all(a in done for a,b in edges if b==v):rec(done+[v])
 rec([]);return out
def griddings(perm,M,q):
 n=len(perm);count=0
 for xs in itertools.combinations_with_replacement(range(n+1),q-1):
  xc=[sum(i>=x for x in xs) for i in range(n)]
  for ys in itertools.combinations_with_replacement(range(n+1),q-1):
   last={};good=True
   for i,y in enumerate(perm):
    c=xc[i];r=sum(y>=v for v in ys);sg=M.get((c,r),0)
    if not sg or ((c,r) in last and (y-last[c,r])*sg<0):good=False;break
    last[c,r]=y
   if good:
    count+=1
    if count>1:return count
 return count
q=int(sys.argv[1]);ell=2*q;rows=list(range(q));cells=[]
for j in range(q):cells.extend([(j,j),((j+1)%q,j)])
cases=0;multi=[]
for signs,colord,roword in itertools.product(itertools.product((-1,1),repeat=2*q),itertools.permutations(rows),itertools.permutations(rows)):
 cs=signs[:q];rs=signs[q:];M={c:cs[c[0]]*rs[c[1]] for c in cells}
 for n in range(2*ell+1,2*ell+2):
  pc=[cells[i%ell] for i in range(n)];ex=[];ey=[]
  pairs=[(i-1,i) for i in range(1,n)]+[(i,i-ell-1) for i in range(ell+1,n)]+[(ell,0)]
  for a,b in pairs:
   if pc[a][0]==pc[b][0]:ex.append((a,b) if cs[pc[a][0]]==1 else (b,a))
   if pc[a][1]==pc[b][1]:ey.append((a,b) if rs[pc[a][1]]==1 else (b,a))
  X=[topo([i for i in range(n) if pc[i][0]==c],ex) for c in rows]
  Y=[topo([i for i in range(n) if pc[i][1]==r],ey) for r in rows]
  for xx in itertools.product(*X):
   for yy in itertools.product(*Y):
    xo=sum((xx[c] for c in colord),[]);yo=sum((yy[r] for r in roword),[]);yr={v:i for i,v in enumerate(yo)};perm=[yr[v] for v in xo]
    if any((xo.index(a)-xo.index(b))*(yr[a]-yr[b])*M[pc[a]]<0 for a in range(n) for b in range(a) if pc[a]==pc[b]):continue
    M2={(colord.index(c),roword.index(r)):sg for (c,r),sg in M.items()};count=griddings(perm,M2,q);cases+=1
    if count!=1:multi.append(dict(signs=signs,n=n,permutation=perm,count=count))
 print('signs',signs,'tested',cases,'failures',len(multi),flush=True)
print(json.dumps(dict(q=q,ell=ell,tested=cases,multiple=multi)),flush=True)
(D/f'coils-ordered-{q}.json').write_text(json.dumps(dict(q=q,ell=ell,tested=cases,multiple=multi),indent=2)+'\n')
