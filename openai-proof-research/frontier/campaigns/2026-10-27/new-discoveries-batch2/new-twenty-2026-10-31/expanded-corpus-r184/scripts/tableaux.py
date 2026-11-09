import pathlib,json,math,sys,collections
D=pathlib.Path(__file__).resolve().parents[1]
# RSK: Des(pi)=Des(Q), Des(pi^-1)=Des(P). For tableaux,
# j is a descent iff the row of j+1 exceeds the row of j.
states={((),-1,0):1}; results=[]
for n in range(1,int(sys.argv[1])+1):
 nxt=collections.defaultdict(int)
 for (shape,last,a),v in states.items():
  for row in range(len(shape)+1):
   if row and (row==len(shape) and shape[-1]==0 or row<len(shape) and shape[row]==shape[row-1]):continue
   t=list(shape)
   if row==len(t):t.append(1)
   else:t[row]+=1
   inc=0 if n==1 else int((row>last)==((n-1)%2==1))
   nxt[(tuple(t),row,a+inc)]+=v
 states=nxt; shapes={}
 for (sh,row,a),v in states.items():
  if sh not in shapes:shapes[sh]=[0]*n
  shapes[sh][a]+=v
 h=[[sum(v[a]*v[b] for v in shapes.values()) for b in range(n)] for a in range(n)]
 assert sum(map(sum,h))==math.factorial(n)
 if n in [11,12]:
  direct=json.loads((D/f'logs/gamma{n}.log').read_text());assert h==direct['hist']
 poly={(a,b):h[a][b] for a in range(n) for b in range(n) if h[a][b]};gam=[]
 for i in range((n-1)//2+1):
  for j in range(n-1-2*i,-1,-1):
   k=n-1-j-2*i;sign=(-1)**i;c=poly.get((n-1-i,i+j),0)*sign
   if c:gam.append([i,j,c])
   for u in range(j+1):
    for b in range(k+1):
     z=(i+u+b,i+u+k-b);poly[z]=poly.get(z,0)-c*sign*math.comb(j,u)*math.comb(k,b)
 assert all(x==0 for x in poly.values()),(n,'basis residual')
 r={'n':n,'permutations':math.factorial(n),'tableau_states':len(states),'shapes':len(shapes),'gamma':gam,'negative':[x for x in gam if x[2]<0]};results.append(r)
 print(json.dumps({k:v for k,v in r.items() if k!='gamma'}),flush=True)
 (D/f'outputs/tableaux{sys.argv[1]}-results.json').write_text(json.dumps(results,indent=2))
