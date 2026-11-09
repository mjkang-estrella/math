import itertools,json,sys
name=sys.argv[1];o=int(sys.argv[2])
if name=='dihedral':
 elems=list(itertools.product(range(o),range(2)))
 def mul(x,y):return ((x[0]+(-1)**x[1]*y[0])%o,(x[1]+y[1])%2)
elidx={x:i for i,x in enumerate(elems)};n=len(elems);tab=[[elidx[mul(x,y)] for y in elems] for x in elems]
trans=[[sum(1<<tab[x][g] for x in range(n) if m>>x&1) for m in range(1<<n)] for g in range(n)]
states={1};D=0
for length in range(1,n+1):
 nxt={}
 for s in states:
  for g in range(1,n):
   t=s|trans[g][s]
   if not(trans[g][s]&1):nxt[t]=True
 print('D',length,'states',len(nxt),flush=True)
 if not nxt:D=length;break
 states=nxt
print('D value',D,flush=True)
states={(1,)+(0,)*n:()}
for length in range(1,D+n+2):
 nxt={}
 for s,w in states.items():
  for g in range(n):
   t=(1,)+tuple(s[r]|trans[g][s[r-1]] for r in range(1,n+1))
   if not(t[n]&1):nxt.setdefault(t,w+(g,))
 print('E',length,'states',len(nxt),'sample',next(iter(nxt.values()),None),flush=True)
 if not nxt:print('E value',length,'conjecture',D+n-1,flush=True);break
 states=nxt
 if len(states)>1200000:print('state cap');break
