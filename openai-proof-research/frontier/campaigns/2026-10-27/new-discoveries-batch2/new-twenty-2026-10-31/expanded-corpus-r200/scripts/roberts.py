import itertools as it,collections as C,pathlib,json,sys,time
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);target=sys.argv[2] if len(sys.argv)>2 else 'all';start=time.monotonic()
def parts(n,m=None):
 if not n:yield ();return
 for a in range(min(n,m or n),1-1,-1):
  for b in parts(n-a,a):yield (a,)+b
shapes=list(parts(n));basis={}
# tableau recursion, row indices of successive entries; English descent iff i+1 lower than i
for sh in shapes:
 counts=C.Counter()
 def rec(rows,seq):
  if len(seq)==n:
   counts[sum(1<<j for j in range(n-1) if seq[j+1]>seq[j])]+=1;return
  for i in range(len(sh)):
   if rows[i]<sh[i] and (not i or rows[i]<rows[i-1]):
    rows[i]+=1;rec(rows,seq+[i]);rows[i]-=1
 rec([0]*len(sh),[])
 v={i:F(x) for i,x in counts.items()};coeff={sh:F(1)}
 for pivot,(w,c) in basis.items():
  if pivot in v:
   a=v[pivot]
   for k,z in w.items():
    v[k]=v.get(k,0)-a*z
    if not v[k]:v.pop(k)
   for k,z in c.items():coeff[k]=coeff.get(k,0)-a*z
 pivot=min(v);a=v[pivot];basis[pivot]=({k:z/a for k,z in v.items()},{k:z/a for k,z in coeff.items()})
perms=list(it.permutations(range(1,n+1)));index={p:i for i,p in enumerate(perms)};positions=[];sigs=[]
for p in perms:
 pos=[0]*(n+1)
 for i,x in enumerate(p):pos[x]=i
 positions.append(pos);sigs.append(sum(1<<(i-1) for i in range(1,n) if pos[i]>pos[i+1]))
yam=[]
for j,p in enumerate(perms):
 tab=[]
 for x in p:
  for row in tab:
   k=next((k for k,z in enumerate(row) if z>x),len(row))
   if k==len(row):row.append(x);break
   row[k],x=x,row[k]
  else:tab.append([x])
 if [z for row in tab for z in row]==list(range(1,n+1)):
  lam=tuple(map(len,tab));block={x:i for i,row in enumerate(tab) for x in row};yam.append((j,lam,[block[x] for x in p]))
rows=[]
for sh in shapes:
 if target!='all' and ','.join(map(str,sh))!=target:continue
 cells=[(r,c) for r,a in enumerate(reversed(sh)) for c in range(a)] # French reading top to bottom; sh already top long as paper
 ci={x:i for i,x in enumerate(cells)};pistols=[(i,ci[(r+1,c)]) for i,(r,c) in enumerate(cells) if (r+1,c) in ci]
 parent=list(range(len(perms)))
 def find(a):
  while parent[a]!=a:parent[a]=parent[parent[a]];a=parent[a]
  return a
 for j,p in enumerate(perms):
  pos=positions[j]
  for i in range(2,n):
   a,b,c=pos[i-1],pos[i],pos[i+1]
   if min(a,c)<b<max(a,c):continue
   q=list(p)
   if any(lo<=min(a,b,c) and max(a,b,c)<=hi for lo,hi in pistols):
    # cycles triples, moving extreme i to opposite extreme
    inds=sorted([a,b,c]);vals=[p[k] for k in inds]
    vals=vals[1:]+vals[:1] if b==inds[0] else vals[-1:]+vals[:-1]
    for k,x in zip(inds,vals):q[k]=x
   else:
    z=a if abs(a-b)>abs(c-b) else c;q[b],q[z]=q[z],q[b]
   k=index[tuple(q)];u,v=find(j),find(k)
   if u!=v:parent[u]=v
 comps={}
 for j in range(len(perms)):comps.setdefault(find(j),C.Counter())[sigs[j]]+=1
 fixed={}
 for j,lam,word in yam:
  jam=False
  for a in range(max(word)):
   left=[i for i,x in enumerate(word) if x==a][::-1];right=[i for i,x in enumerate(word) if x==a+1][::-1]
   for k in range(min(len(left),len(right)-1)):
    lo,hi=sorted([left[k],right[k+1]])
    if any(x<=lo and hi<=y for x,y in pistols):jam=True
  if not jam:fixed.setdefault(find(j),C.Counter())[lam]+=1
 for root,counts in comps.items():
  v={i:F(x) for i,x in counts.items()};coeff={}
  for pivot,(w,c) in basis.items():
   if pivot in v:
    a=v[pivot]
    for k,z in w.items():
     v[k]=v.get(k,0)-a*z
     if not v[k]:v.pop(k)
    for k,z in c.items():coeff[k]=coeff.get(k,0)+a*z
  if v or any(x<0 or x.denominator!=1 for x in coeff.values()) or any(z>coeff.get(lam,0) for lam,z in fixed.get(root,{}).items()):
   out={'shape':sh,'root':perms[root],'fixed':{str(k):z for k,z in fixed.get(root,{}).items()},'counts':dict(counts),'residual':{str(k):str(z) for k,z in v.items()},'schur':{str(k):str(z) for k,z in coeff.items()}}
   (D/f'outputs/roberts-obstruction-{n}.json').write_text(json.dumps(out,indent=2));print('OBSTRUCTION',out,flush=True);sys.exit(1)
 rows.append({'shape':sh,'permutations':len(perms),'components':len(comps),'fixed_words':sum(sum(x.values()) for x in fixed.values())});print(rows[-1],flush=True)
(D/f'outputs/roberts-fixed-{n}-{target}.json').write_text(json.dumps({'rows':rows,'seconds':time.monotonic()-start,'limitation':'Schur positivity and fixed-word coefficient-capacity necessary conditions only; full signature-preserving injection not checked'},indent=2))
