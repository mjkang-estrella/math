import pathlib,sys,itertools,json,ctypes as C
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
# Bind LP library independently, no execution of previous experiment.
L=C.CDLL('/lib64/liblpsolve55.so');P=C.c_void_p;I=C.c_int;R=C.c_double
spec={'make_lp':(P,[I,I]),'add_constraintex':(C.c_ubyte,[P,I,C.POINTER(R),C.POINTER(I),I,R]),'set_bounds':(C.c_ubyte,[P,I,R,R]),'set_verbose':(None,[P,I]),'set_timeout':(None,[P,C.c_long]),'solve':(I,[P]),'get_variables':(C.c_ubyte,[P,C.POINTER(R)]),'delete_lp':(None,[P])}
for f,(res,args) in spec.items():getattr(L,f).restype=res;getattr(L,f).argtypes=args
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for d,r in [(2,2),(3,2),(4,2),(3,3)]:
 coords=[frozenset(s) for k in range(1,r+1) for s in itertools.combinations(range(d),k)];n=len(coords)
 keys=[('c',)]+[('s',k) for k in range(1,r+1)]+sorted({('p',len(a),len(b),len(a&b)) for a,b in itertools.combinations(coords,2)})
 lp=L.make_lp(0,len(keys));L.set_verbose(lp,1);L.set_timeout(lp,30)
 for i,k in enumerate(keys):L.set_bounds(lp,i+1,-1e30,0 if k[0]=='p' else 1e30)
 F={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(1<<d)}
 for x in range(1<<n):
  selected=[s for j,s in enumerate(coords) if x>>j&1];v={k:0 for k in keys};v[('c',)]=1
  for a in selected:v[('s',len(a))]+=1
  for a,b in itertools.combinations(selected,2):v[('p',len(a),len(b),len(a&b))]+=1
  L.add_constraintex(lp,len(keys),(R*len(keys))(*(v[k] for k in keys)),(I*len(keys))(*range(1,len(keys)+1)),1 if x in F else 2,-1 if x in F else 0)
 status=L.solve(lp);a=(R*len(keys))();L.get_variables(lp,a);q={'d':d,'r':r,'status':status,'coefficients':list(zip(keys,list(a)))};out.append(q);L.delete_lp(lp);print(q,flush=True)
(D/'outputs/quadratic-search.json').write_text(json.dumps(out,indent=2))
