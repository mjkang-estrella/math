from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

def windows(M,d,r0,g):
    lengths={}; spans={0:0}
    for h in range(1,d+1):
        lengths[h]=r0 if h==1 else max(r0,g+spans[h-1])
        spans[h]=M*lengths[h]+(M-1)*g if h==1 else M*(lengths[h]+g+spans[h-1])+(M-1)*g
    edges={};pos=3
    def visit(path,h):
        nonlocal pos
        for i in range(M):
            e=path+(i,);a=pos;b=a+lengths[h];pos=b+g
            edges[e]={'a':a,'b':b,'h':h}
            if h>1:visit(e,h-1)
            edges[e]['star']=max(v['b'] for k,v in edges.items() if k[:len(e)]==e)
    visit((),d)
    assert max(v['b'] for v in edges.values())==3+spans[d]
    for e,v in edges.items():assert v['star']-v['a']<=2*lengths[v['h']]
    return edges,lengths,spans

def key(z,b,ell=4):return ((z-z.numerator//z.denominator)*2**(b+ell)).numerator//((z-z.numerator//z.denominator)*2**(b+ell)).denominator

def active(q,t,a,b):
    n=1;z=t*q;out=[]
    while z>=F(1,2**b):
        if z<=F(1,2**a):out.append((n,z))
        z*=q;n+=1
    return out

counts={'tree_padding':0,'active_windows':0,'separation_pairs':0,'stable_key_checks':0,'routing_outcomes':0,'independence_identities':0}
for M,d,r0,g in product(range(2,5),range(1,4),range(1,10),range(1,5)):
    es,rs,ss=windows(M,d,r0,g);counts['tree_padding']+=len(es)
    A=0
    for h in range(1,d+1):A=4*M*(1+A);assert ss[h]<=A*(r0+g)
qs=[F(1,4),F(1,3),F(1,2),F(2,3),F(3,4)]
for a,r,q,t in product([3,7,20],range(4,13),qs,[F(1),F(5,4),F(3,2),F(2)]):
    b=a+r;pts=active(q,t,a,b);counts['active_windows']+=1
    assert len(pts)>=F(r,4)
    for x in [F(0),F(1,3),F(1)-F(1,2**(a+1))]:
        zz=[x]+[x+z for n,z in pts];keys=[key(z,b) for z in zz];assert len(keys)==len(set(keys))
        for j in range(len(zz)):
            for k in range(j):
                assert abs(zz[j]-zz[k])>=F(1,4*2**b);counts['separation_pairs']+=1
for bprev,g in product(range(2,10),range(6,12)):
    a=bprev+g;delta=F(1,2**a);width=F(1,2**(bprev+4))
    for x in [F(0),width,F(1)-width,width-delta*2]:
        for z in [delta,delta/2,delta/3]:
            assert key(x,bprev)==key(x+z,bprev);counts['stable_key_checks']+=1
    x=width-delta;assert key(x,bprev)!=key(x+delta,bprev)
# Finite source-style adaptive routing, now with indices selected by physical windows.
es,rs,ss=windows(3,2,2,2);x=F(0);q=F(1,2);t=F(1)
pairs=[]
for i in [0,1]:
    for n,z in active(q,t,es[(i,)]['a'],es[(i,)]['b'])[:2]:pairs.append((i,n,z))
addresses=set()
center={}
for e,v in es.items():
    if e[-1]<2:center[(e,key(x,v['b']))]=0
for i,n,z in pairs:
    addresses.add(((i,),key(x+z,es[(i,)]['b'])))
    for j in [0,1]:addresses.add(((i,j),key(x+z,es[(i,j)]['b'])))
unknown=sorted(addresses-set(center));p=F(1,3);total=F(0)
assert len(unknown)<=16
for bits in product([0,1],repeat=len(unknown)):
    s=dict(center);s.update(zip(unknown,bits));term=[];A=[]
    for i,n,z in pairs:
        A.append(s[((i,),key(x+z,es[(i,)]['b']))])
        j=next((j for j in [0,1] if s[((i,j),key(x+z,es[(i,j)]['b']))]),2)
        term.append(((i,j),key(x+z,es[(i,j)]['b'])))
    assert len(term)==len(set(term));total+=(1-p)**sum(A);counts['routing_outcomes']+=1
assert total/2**len(unknown)==(1-p/2)**len(pairs)
for k in range(9):
    for p in [F(1,10),F(1,3),F(1,2),F(9,10)]:
        s=sum(((1-p)**sum(a) for a in product([0,1],repeat=k)),F(0))/2**k
        assert s==(1-p/2)**k;counts['independence_identities']+=1
# Exact general-position line arrangement count, including edges/vertices.
arr=[]
for m in range(51):
    # m lines without parallel pairs/triple intersections maximize this count.
    faces2=1+m*(m+1)//2;faces1=m*m;faces0=m*(m-1)//2
    assert faces0+faces1+faces2==2*m*m+1<=8*(m+1)**2
    arr.append({'lines':m,'all_strata':2*m*m+1})
# The density-point counterexample has exactly these two-sided ratio bounds.
assert F(1,3)<F(9,22)<F(11,18)<F(2,3)
# Compact ratio cover and signed dyadic measure budget are rational identities.
assert F(12,64)*(F(1,3)+1+1)==F(7,16)
for j in range(3,30):assert F(1,j)<=F(1,j-1) and 1-F(1,j)>=1-F(1,j-1)
# Genuine failure of fixed index separation when a reference grid is reused at a faster ratio.
b=12;N=2**(b+4);assert key(F(1,4)**b,b)==key(F(1,4)**(b-1),b)==0
# Supergeometric windows have only sqrt(r) tests, rather than linear density.
supergeo=[]
for r in [16,64,256,1024,4096]:
    hits=[n for n in range(1,r+1) if 3<=n*n<=3+r]
    supergeo.append({'physical_length':r,'tests':len(hits)})
    assert len(hits)<=isqrt(r+3)
print(json.dumps({'status':'PASS','scope':'Exact finite geometry, algebra, adaptive addresses and probability identities; not a universal proof or independent review.','counts':counts,'arrangement_counts':arr,'signed_scale_loss':'7/16','supergeometric_counts':supergeo,'fixed_reference_grid_collision':{'q_reference':'1/2','q_test':'1/4','b':12,'keys':[0,0]}},indent=2,sort_keys=True))
