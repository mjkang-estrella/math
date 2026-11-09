import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1]
def words(n,w=(),a=0,b=0,c=0):
 if a+b+c==3*n:yield w;return
 if a<n:yield from words(n,w+(0,),a+1,b,c)
 if b<a:yield from words(n,w+(1,),a,b+1,c)
 if c<a:yield from words(n,w+(2,),a,b,c+1)
def evac(w,dual=False):
 w=list(w);L=len(w)
 schedule=([range(j-1,L-1) for j in range(L-1,0,-1)] if dual else [range(j) for j in range(L-1,0,-1)])
 for sweep in schedule:
  for i in sweep:
   # Only prefix ending at i changes on an adjacent swap.
   if w[i]==w[i+1]:continue
   counts=[0,0,0]
   for x in w[:i]:counts[x]+=1
   counts[w[i+1]]+=1
   if counts[0]>=counts[1] and counts[0]>=counts[2]:w[i],w[i+1]=w[i+1],w[i]
 return tuple(w)
out=[]
for n in range(1,6):
 total=f=g=0
 for w in words(n):
  total+=1;f+=evac(w)==w;g+=evac(w,True)==w
 expected=3**(n//2)*4**((n+1)//2)*math.prod(3*j-1 for j in range(1,n//2+1))*math.prod(3*j-2 for j in range(1,(n+1)//2+1))//math.factorial(n+1)
 a={'n':n,'total':total,'evac':f,'evac_dual':g,'predicted_dual':expected,'predicted_evac':expected if n%2==0 else 0};out.append(a);print(a,flush=True);(D/'outputs/kreweras-search.json').write_text(json.dumps(out,indent=2))
