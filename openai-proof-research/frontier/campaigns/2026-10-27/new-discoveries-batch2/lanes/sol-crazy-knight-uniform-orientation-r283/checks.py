import pathlib,json,math,itertools,hashlib
L=pathlib.Path(__file__).resolve().parent
def compose(a,b):return [a[x] for x in b]
def inv(a):
 b=[0]*len(a)
 for i,x in enumerate(a):b[x]=i
 return b
def cycles(p):
 seen=set();out=[]
 for i in range(len(p)):
  if i in seen:continue
  c=[];j=i
  while j not in seen:seen.add(j);c.append(j);j=p[j]
  assert j==i;out.append(c)
 return out
def board(n,k,R=(),C=()):
 cells=[(i,j) for i in range(n) for j in range(n) if (i-j)%n<k];idx={x:a for a,x in enumerate(cells)}
 rows=[[idx[i,j] for j in range(n) if (i,j) in idx] for i in range(n)]
 cols=[[idx[i,j] for i in range(n) if (i,j) in idx] for j in range(n)]
 def perm(lists,neg):
  p=list(range(n*k))
  for t,a in enumerate(lists):
   for z,x in enumerate(a):p[x]=a[(z+(-1 if t in neg else 1))%k]
  return p
 return cells,rows,cols,perm(rows,R),perm(cols,C)
def reduced(n,k,E):
 s=k-1;E=sorted(E);w=len(E);p=list(range(n));pos={x:a for a,x in enumerate(E)}
 for x in range(n):p[x]=((E[(pos[x]+s)%w] if x in pos else x)-s)%n
 return p
def switch(p,ordered):
 # Exact cut successor: start at selected vertex, follow p to next selected vertex.
 U=set(ordered);rho={}
 for u in ordered:
  v=p[u]
  while v not in U:v=p[v]
  rho[u]=v
 q={ordered[i]:ordered[(i-2)%len(ordered)] for i in range(len(ordered))}
 induced=[ordered.index(q[rho[u]]) for u in ordered]
 untouched=sum(not (set(c)&U) for c in cycles(p))
 return untouched+len(cycles(induced))
def main():
 out={'scope':'diagnostics only','identity_cases':0,'interval_failures':[],'exceptional_interval':[],'local_minima':[]}
 for n in range(3,16,2):
  for k in range(3,n+1,2):
   cells,rows,cols,H,V=board(n,k);p=compose(V,H)
   assert len(cycles(p))==k-1+math.gcd(n,k-1)
   for E in [set(),{0},{0,1},{0,2,3} & set(range(n)),set(range(min(n,5)))]:
    _,_,_,HE,VE=board(n,k,C=E);actual=compose(VE,HE)
    D=list(range(n*k))
    for j in E:
     for z,u in enumerate(cols[j]):D[u]=cols[j][(z-2)%k]
    assert actual==compose(D,p)
    # Source return map is for reversed ROWS and uniform columns.
    _,_,_,HR,VR=board(n,k,R=E);pr=compose(VR,HR)
    if E and {x%math.gcd(n,k-1) for x in E}==set(range(math.gcd(n,k-1))):
     assert (len(cycles(pr))==1)==(len(cycles(reduced(n,k,E)))==1)
    for j in range(n):
     _,_,_,HC,VC=board(n,k,C=E^{j});pc=compose(VC,HC)
     # If currently reversed, the flip multiplier is +2 instead of -2.
     order=cols[j] if j not in E else list(reversed(cols[j]))
     assert len(cycles(pc))==switch(actual,order)
    # Row flip multiplier V H_i^-2 V^-1.
    for i in range(n):
     A=list(range(n*k))
     for z,u in enumerate(rows[i]):A[VE[u]]=VE[rows[i][(z-2)%k]]
     _,_,_,HN,VN=board(n,k,R={i},C=E)
     assert compose(VN,HN)==compose(A,actual)
    out['identity_cases']+=1
 for k in range(3,100,2):
  for n in range(k+2,2*k+1,2):
   g=math.gcd(n,k-1)
   if g==1:continue
   wins=[]
   for w in range(g,n+1,2):
    if len(cycles(reduced(n,k,set(range(w)))))==1:wins.append(w)
   rec=dict(n=n,k=k,g=g,w=wins)
   if not wins:out['interval_failures'].append(rec)
   if math.gcd(g+1,k-1)>2 and len(out['exceptional_interval'])<12:out['exceptional_interval'].append(rec)
 # Mixed-sign greedy descent; preserve genuine traps as failures, not impossibility.
 for n,k in [(9,7),(15,13),(27,25),(33,31)]:
  R=set();C=set();path=[]
  for step in range(30):
   cells,rows,cols,H,V=board(n,k,R,C);p=compose(V,H);count=len(cycles(p));path.append(count)
   if count==1:break
   best=(count,None,None)
   for side in [0,1]:
    for i in range(n):
     _,_,_,HH,VV=board(n,k,R^{i} if side==0 else R,C^{i} if side==1 else C)
     z=len(cycles(compose(VV,HH)))
     if z<best[0]:best=(z,side,i)
   if best[1] is None:break
   (R if best[1]==0 else C).symmetric_difference_update({best[2]})
  rec=dict(n=n,k=k,R=sorted(R),C=sorted(C),cycle_counts=path)
  pairbest=count; witness=None
  for (side,i),(side2,j) in itertools.combinations(itertools.product(range(2),range(n)),2):
   RR=R.copy();CC=C.copy()
   (RR if side==0 else CC).symmetric_difference_update({i})
   (RR if side2==0 else CC).symmetric_difference_update({j})
   _,_,_,HH,VV=board(n,k,RR,CC);z=len(cycles(compose(VV,HH)))
   if z<pairbest:pairbest=z;witness=[side,i,side2,j]
  rec.update(best_two_flip=pairbest,two_flip_witness=witness)
  out['local_minima'].append(rec)
 (L/'exact-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
