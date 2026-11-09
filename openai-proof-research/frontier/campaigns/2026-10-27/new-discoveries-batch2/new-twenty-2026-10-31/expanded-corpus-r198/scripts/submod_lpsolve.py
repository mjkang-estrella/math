import ctypes as C,itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
L=C.CDLL('/lib64/liblpsolve55.so');P=C.c_void_p;I=C.c_int;R=C.c_double
spec={'make_lp':(P,[I,I]),'add_constraintex':(C.c_ubyte,[P,I,C.POINTER(R),C.POINTER(I),I,R]),'set_bounds':(C.c_ubyte,[P,I,R,R]),'set_verbose':(None,[P,I]),'set_timeout':(None,[P,C.c_long]),'solve':(I,[P]),'get_variables':(C.c_ubyte,[P,C.POINTER(R)]),'delete_lp':(None,[P])}
for f,(res,args) in spec.items():getattr(L,f).restype=res;getattr(L,f).argtypes=args
out=[]
for d,r in [(2,2),(3,2),(3,3),(4,2)]:
 coords=[s for k in range(1,r+1) for s in itertools.combinations(range(d),k)];n=len(coords);N=1<<n
 fam={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(1<<d)}
 lp=L.make_lp(0,N);L.set_verbose(lp,1);L.set_timeout(lp,50)
 for x in range(N):L.set_bounds(lp,x+1,-1e30 if x in fam else 0,-1 if x in fam else 1e30)
 count=0
 for i in range(n):
  for j in range(i+1,n):
   for x in range(N):
    if x&(1<<i|1<<j):continue
    indices=(I*4)(x+1,(x|1<<i|1<<j)+1,(x|1<<i)+1,(x|1<<j)+1)
    assert L.add_constraintex(lp,4,(R*4)(1,1,-1,-1),indices,1,0);count+=1
 status=L.solve(lp);record={'d':d,'r':r,'nonempty_coordinates':n,'variables':N,'constraints':count,'status':status,'diagnostic_only':True}
 if status==0:
  a=(R*N)();L.get_variables(lp,a);v=list(a);record['min_value']=min(v);record['max_value']=max(v);record['integral']=all(abs(z-round(z))<1e-6 for z in v);(D/'outputs'/f'submod-values-{d}-{r}.json').write_text(json.dumps(v))
 L.delete_lp(lp);out.append(record);print(record,flush=True);(D/'outputs/submodular-search.json').write_text(json.dumps(out,indent=2))
