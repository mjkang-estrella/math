import pathlib,json,itertools,collections
P=pathlib.Path(__file__).parent
out=[]
def weights(n,q,s):
 w=[0]*s
 for i in range(n+1):w.append(1+(q-1)*sum(w[-s:]))
 return w[s:-1],w[-1]
phi=[(1,1),(0,1),(1,0),(0,0)]
for n in range(1,8):
 w,m=weights(n,4,1);v,t=weights(2*n,2,2);classes=collections.defaultdict(list)
 for x in itertools.product(range(4),repeat=n):classes[sum(a*b for a,b in zip(w,x))%m].append(x)
 mx=max(map(len,classes.values()));maxa=[a for a,x in classes.items() if len(x)==mx];tests=[]
 binary=collections.Counter(sum(a*b for a,b in zip(v,x))%t for x in itertools.product(range(2),repeat=2*n))
 for a in maxa:
  image_residues=collections.Counter(sum(u*z for u,z in zip(v,itertools.chain.from_iterable(phi[c] for c in x)))%t for x in classes[a])
  tests.append({'a':a,'size':mx,'image_residues':dict(image_residues),'equal_to_single_binary_class':len(image_residues)==1 and binary[next(iter(image_residues))]==mx})
 out.append({'n':n,'quaternary_weights':w,'quaternary_modulus':m,'binary_weights':v,'binary_modulus':t,'maximum_classes':tests})
(P/'bounded-checks.json').write_text(json.dumps({'executed':True,'range':'1<=n<=7; all maximum residues; fixed source phi9; exhaustive word enumeration','no_universal_conclusion':True,'results':out},indent=2)+'\n')
for o in out:print(o['n'],[(t['a'],t['size'],t['equal_to_single_binary_class']) for t in o['maximum_classes']][:15])
