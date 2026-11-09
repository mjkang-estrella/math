# One-step map for equal group size B: (x,y) in comps(u,B) x comps(v,B), v>=u+2 -> comps(u+1,B) x comps(v-1,B).
# k = first index with G_k=Y_k-X_k >= D-1 (D=v-u); t=G_k-(D-1); x'=(x_<k, x_k+t, y_>k), y'=(y_<k, y_k-t, x_>k).
import sys,itertools
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
def comps(n,m):
    if m==1: yield (n,); return
    for i in range(n+1):
        for r in comps(n-i,m-1): yield (i,)+r
def dom(p,q):
    p=sorted(p,reverse=True); q=sorted(q,reverse=True); sp=sq=0
    for a,b in zip(p,q):
        sp+=a; sq+=b
        if sp<sq: return False
    return True
def fmap(x,y,u,v):
    D=v-u; G=0
    for k in range(len(x)):
        G+=y[k]-x[k]
        if G>=D-1:
            t=G-(D-1)
            return x[:k]+(x[k]+t,)+y[k+1:], y[:k]+(y[k]-t,)+x[k+1:]
    raise Exception
B_max=int(sys.argv[1]); V=int(sys.argv[2])
bad=0; tot=0
for B in range(1,B_max+1):
  for v in range(2,V+1):
    for u in range(0,v-1):
      img={}; coll=0; domfail=0
      for x in comps(u,B):
        for y in comps(v,B):
          x2,y2=fmap(x,y,u,v)
          assert sum(x2)==u+1 and sum(y2)==v-1 and min(x2+y2)>=0
          if not dom(x+y,x2+y2): domfail+=1
          if (x2,y2) in img: coll+=1
          img[(x2,y2)]=(x,y)
      tot+=1
      if coll or domfail:
        bad+=1
        if bad<10: print('B',B,'u',u,'v',v,'collisions',coll,'domfail',domfail)
print('cases',tot,'bad',bad)
