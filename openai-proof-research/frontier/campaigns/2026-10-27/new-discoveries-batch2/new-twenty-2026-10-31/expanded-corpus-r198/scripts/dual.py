import pathlib,sys,itertools,json,ctypes as C,fractions,math
D=pathlib.Path(__file__).resolve().parents[1]
L=C.CDLL('/lib64/liblpsolve55.so');P=C.c_void_p;I=C.c_int;R=C.c_double
for f,res,args in [('make_lp',P,[I,I]),('add_constraintex',C.c_ubyte,[P,I,C.POINTER(R),C.POINTER(I),I,R]),('set_verbose',None,[P,I]),('set_timeout',None,[P,C.c_long]),('solve',I,[P]),('get_variables',C.c_ubyte,[P,C.POINTER(R)]),('delete_lp',None,[P])]:getattr(L,f).restype=res;getattr(L,f).argtypes=args
# d=5,r=2, omit always-one empty coordinate; all actions are permutations of the five variables.
d=5;coords=[tuple(s) for k in [1,2] for s in itertools.combinations(range(d),k)];n=len(coords);N=1<<n;idx={s:i for i,s in enumerate(coords)}
maps=[[1<<idx[tuple(sorted(p[a] for a in s))] for s in coords] for p in itertools.permutations(range(d))]
orbit=[-1]*N;reps=[]
for x in range(N):
 if orbit[x]>=0:continue
 label=len(reps);reps.append(x);bits=[j for j in range(n) if x>>j&1]
 for p in maps:orbit[sum(p[j] for j in bits)]=label
fam={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(1<<d)}
rows={}
for x in reps:
 for i in range(n):
  if x>>i&1:continue
  for j in range(i+1,n):
   if x>>j&1:continue
   terms=[(x,1),(x|1<<i|1<<j,1),(x|1<<i,-1),(x|1<<j,-1)];coeff={}
   for y,c in terms:coeff[orbit[y]]=coeff.get(orbit[y],0)+c
   row=tuple(sorted((k,v) for k,v in coeff.items() if v))
   if row:rows.setdefault(row,{'kind':'submodular','terms':terms})
rowlist=[(dict(k),v) for k,v in rows.items()]
for k,x in enumerate(reps):rowlist.append(({k:1 if x in fam else -1},{'kind':'good' if x in fam else 'bad','point':x}))
M=len(rowlist);lp=L.make_lp(0,M);L.set_verbose(lp,1);L.set_timeout(lp,95)
for k in range(len(reps)):
 terms=[(j+1,row.get(k,0)) for j,(row,meta) in enumerate(rowlist) if row.get(k,0)]
 assert L.add_constraintex(lp,len(terms),(R*len(terms))(*(v for j,v in terms)),(I*len(terms))(*(j for j,v in terms)),3,0)
inds=[j+1 for j,(row,meta) in enumerate(rowlist) if meta['kind']=='good']
L.add_constraintex(lp,len(inds),(R*len(inds))(*(1 for j in inds)),(I*len(inds))(*inds),3,1)
status=L.solve(lp);print('dual',status,flush=True)
if status==0:
 a=(R*M)();L.get_variables(lp,a);support=[(j,fractions.Fraction(v).limit_denominator(1000000)) for j,v in enumerate(a) if v>1e-8];den=math.lcm(*(v.denominator for j,v in support));weights=[(j,int(v*den)) for j,v in support];balance=[0]*len(reps)
 for j,w in weights:
  for k,v in rowlist[j][0].items():balance[k]+=w*v
 exact=all(v==0 for v in balance);certificate={'status':status,'exact_balance':exact,'denominator':den,'support':[dict(rowlist[j][1],weight=w) for j,w in weights],'reps':reps,'orbit':orbit,'coords':coords};(D/'outputs/submod-dual.json').write_text(json.dumps(certificate,indent=2));print('support',len(weights),'exact',exact,'weights',weights,flush=True)
L.delete_lp(lp)
