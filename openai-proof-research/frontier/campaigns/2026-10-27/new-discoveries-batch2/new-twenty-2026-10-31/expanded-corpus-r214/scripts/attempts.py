import pathlib,json,sys,math,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1]
if mode=='q':
 N=int(sys.argv[2]);M=int(sys.argv[3]);res=[]
 for m in range(4,M+1):
  a=[0]*(N+1);a[0]=1
  for j in range(1,N+1,m):
   for n in range(j,N+1):a[n]+=a[n-j]
  for j in range(m-1,N+1,m):
   for n in range(j,N+1):a[n]-=a[n-j]
  neg=[(i,x) for i,x in enumerate(a) if x<0]
  res.append({'m':m,'N':N,'negative':neg[:5],'zeros_positive_degree':sum(x==0 for x in a[1:]),'sha256':hashlib.sha256(json.dumps(a).encode()).hexdigest()})
  print(m,'neg',neg[:1],flush=True)
 (D/f'outputs/q-{N}-{M}.json').write_text(json.dumps(res,indent=2))
elif mode=='semigroup':
 # Enumerate all semigroups of genus <= G via effective-generator deletion.
 # Store conductor and positive nongaps <= 2G+1 as bitsets; child deletion x >= conductor.
 G=int(sys.argv[2]);L=2*G+3;full=(1<<L)-1;level=[full];rows=[]
 for g in range(G+1):
  counts={};nxt=[]
  for s in level:
   gaps=(full^s);c=max(1,gaps.bit_length());m=next(i for i in range(1,L) if s>>i&1)
   counts[m]=counts.get(m,0)+1
   if g==G:continue
   for x in range(max(c,m),min(c+m,L)):
    if not(s>>x&1):continue
    if any((s>>a&1) and (s>>(x-a)&1) for a in range(m,x//2+1)):continue
    nxt.append(s^(1<<x))
  rows.append({'genus':g,'total':len(level),'multiplicity_counts':counts});print(g,len(level),flush=True);level=nxt
 bad=[]
 for a,b in zip(rows,rows[1:]):
  for m,v in a['multiplicity_counts'].items():
   if m>=2 and v>b['multiplicity_counts'].get(m,0):bad.append((m,a['genus'],v,b['multiplicity_counts'].get(m,0)))
 (D/f'outputs/semigroups-{G}.json').write_text(json.dumps({'rows':rows,'violations':bad},indent=2))
elif mode=='hook':
 # Q=1-integral J1(2z)/z; its EGF coefficients q_(2j+1)=(-1)^(j+1) Catalan(j), others zero.
 # A=-log Q and Q*A'=-Q' gives integer recurrence for A_n.
 N=int(sys.argv[2]);q=[0]*(N+1);q[0]=1
 for j in range((N+1)//2):q[2*j+1]=(-1)**(j+1)*math.comb(2*j,j)//(j+1)
 a=[0]*(N+1)
 for n in range(1,N+1):a[n]=-q[n]-sum(math.comb(n-1,i)*q[i]*a[n-i] for i in range(1,n))
 bad=[n for n in range(3,N+1) if (a[n]%2==1)!=((n+1)&n==0)]
 (D/f'outputs/hooks-{N}.json').write_text(json.dumps({'N':N,'violations':bad,'values':[str(x) for x in a]},indent=2));print('N',N,'violations',bad,'first',a[:15])
