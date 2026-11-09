import sys,random,itertools,collections
mode=sys.argv[1]
if mode=='boolean':
 def ft(a):
  a=a[:];h=1
  while h<len(a):
   for i in range(0,len(a),h*2):
    for j in range(i,i+h):a[j],a[j+h]=a[j]+a[j+h],a[j]-a[j+h]
   h*=2
  return a
 for n in range(1,5):
  N=1<<n;fs=[]
  for mask in range(1<<N):
   a=[mask>>i&1 for i in range(N)]
   if all(a[x]<=a[x|1<<i] for x in range(N) for i in range(n)):
    fs.append((mask,sum(a),ft(a)))
  worst=None;checked=0
  for f,sf,F in fs:
   for g,sg,G in fs:
    cov=(f&g).bit_count()*N-sf*sg
    rhs=4*sum(s.bit_count()*F[s]**2*G[s]**2 for s in range(1,N))
    gap=cov*N*N-rhs;assert gap>=0
    if rhs:worst=min(worst or (cov*N*N,rhs),(cov*N*N,rhs),key=lambda v:v[0]/v[1])
    checked+=1
  print(dict(n=n,functions=len(fs),ordered_pairs=checked,min_ratio_to_rhs=worst),flush=True)
elif mode=='andre':
 q=4;Q=64;poly=0b1000011
 def mul(a,b):
  c=0
  while b:
   if b&1:c^=a
   a<<=1
   if a&64:a^=poly
   b>>=1
  return c
 tab=[[mul(a,b) for b in range(Q)]for a in range(Q)]
 def pw(a,e):
  r=1
  while e:
   if e&1:r=tab[r][a]
   a=tab[a][a];e//=2
  return r
 inv=[0]+[pw(a,62)for a in range(1,Q)];norm=[pw(a,21)for a in range(Q)]
 deltas=sorted(set(norm[1:]));cnt=collections.Counter();exceptions=[]
 # All x=t, y=A*t+B*t², A,B nonzero. T is F; N=(1,A) is neither E nor F.
 for A in range(1,Q):
  for B in range(1,Q):
   pts=[(t,tab[A][t]^tab[B][tab[t][t]])for t in range(1,Q)]
   for m in (1,2):
    u=[tab[y][inv[pw(x,q**m)]]for x,y in pts]
    for d in deltas:
     vals=[v for v in u if norm[v]==d];ok=len(vals)==len(set(vals));cnt['arcs' if ok else 'nonarcs']+=1
     if ok:exceptions.append((A,B,m,d))
 print(dict(q=q,field_modulus=poly,family='x=t,y=A*t+B*t²; A,B nonzero',conics=63**2,replacements=sum(cnt.values()),counts=dict(cnt),exceptions=exceptions[:10]),flush=True)
