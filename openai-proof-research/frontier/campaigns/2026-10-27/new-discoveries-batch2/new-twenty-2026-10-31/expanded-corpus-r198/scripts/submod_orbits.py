import pathlib,sys,itertools,json,ctypes as C
D=pathlib.Path(__file__).resolve().parents[1]
L=C.CDLL('/lib64/liblpsolve55.so');P=C.c_void_p;I=C.c_int;R=C.c_double
for f,res,args in [('make_lp',P,[I,I]),('add_constraintex',C.c_ubyte,[P,I,C.POINTER(R),C.POINTER(I),I,R]),('set_bounds',C.c_ubyte,[P,I,R,R]),('set_verbose',None,[P,I]),('set_timeout',None,[P,C.c_long]),('solve',I,[P]),('get_variables',C.c_ubyte,[P,C.POINTER(R)]),('delete_lp',None,[P])]:getattr(L,f).restype=res;getattr(L,f).argtypes=args
for d,r in [(4,3),(5,2)]:
 coords=[tuple(s) for k in range(1,r+1) for s in itertools.combinations(range(d),k)];n=len(coords);N=1<<n;idx={s:i for i,s in enumerate(coords)}
 maps=[[1<<idx[tuple(sorted(p[a] for a in s))] for s in coords] for p in itertools.permutations(range(d))]
 orbit=[-1]*N;reps=[]
 for x in range(N):
  if orbit[x]>=0:continue
  label=len(reps);reps.append(x);bits=[j for j in range(n) if x>>j&1]
  for p in maps:orbit[sum(p[j] for j in bits)]=label
 print('orbits',d,r,len(reps),flush=True)
 fam={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(1<<d)}
 constraints=set()
 # Each orbit representative and all coordinate pairs suffices, by symmetry.
 for x in reps:
  for i in range(n):
   if x>>i&1:continue
   for j in range(i+1,n):
    if x>>j&1:continue
    coeff={}
    for y,c in [(x,1),(x|1<<i|1<<j,1),(x|1<<i,-1),(x|1<<j,-1)]:coeff[orbit[y]]=coeff.get(orbit[y],0)+c
    constraints.add(tuple(sorted((k,v) for k,v in coeff.items() if v)))
 lp=L.make_lp(0,len(reps));L.set_verbose(lp,1);L.set_timeout(lp,70)
 for k,x in enumerate(reps):L.set_bounds(lp,k+1,-1e30 if x in fam else 0,-1 if x in fam else 1e30)
 for row in constraints:
  if row:assert L.add_constraintex(lp,len(row),(R*len(row))(*(v for k,v in row)),(I*len(row))(*(k+1 for k,v in row)),1,0)
 status=L.solve(lp);rec={'d':d,'r':r,'face_points':N,'orbits':len(reps),'constraints':len(constraints),'status':status,'note':'Symmetric restriction loses no feasibility, by averaging; floating LP diagnostic only.'}
 if status==0:
  a=(R*len(reps))();L.get_variables(lp,a);(D/'outputs'/f'orbit-values-{d}-{r}.json').write_text(json.dumps({'reps':reps,'values':list(a)}))
 L.delete_lp(lp);(D/'outputs'/f'orbit-search-{d}-{r}.json').write_text(json.dumps(rec,indent=2));print(rec,flush=True)
