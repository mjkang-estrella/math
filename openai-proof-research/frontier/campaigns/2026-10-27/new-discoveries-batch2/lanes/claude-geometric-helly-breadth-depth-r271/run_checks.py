"""Consolidated exact checks for r271 (diagnostic; run under the prescribed helper guard)."""
import sys,random,math,json,hashlib;sys.path.insert(0,'.')
from fractions import Fraction as F
from itertools import combinations
from csc import hull,on_boundary_all,data,admissible,csc_center
from csc2 import center,is_min_obstruction
from topo import pieces,feasible,inM
import model
out={}
def S(p):return [str(p[0]),str(p[1])] if isinstance(p,tuple) and len(p)==2 else str(p)
# 1 Lemma A vs brute-force hull boundary test
random.seed(1);mm=cnt=0
for t in range(80):
    n=random.randint(3,7);ang=sorted(random.random()*6.283 for _ in range(n))
    X=[(F(round(100*math.cos(a)*(1+random.random()*0.3))),F(round(100*math.sin(a)))) for a in ang]
    if len(set(X))<n or not on_boundary_all(X,hull(X)): continue
    L,N=data(X)
    for O in [(F(i*20),F(j*20)) for i in range(-5,6) for j in range(-5,6)]:
        Z=X+[(2*O[0]-x[0],2*O[1]-x[1]) for x in X];H=hull(Z)
        mm+=admissible(X,O,L,N)!=(len(H)>=3 and on_boundary_all(Z,H));cnt+=1
out['lemmaA_vs_bruteforce']=dict(pairs=cnt,mismatches=mm)
# 2 source nine-point example (rational approximation of the stated construction)
def rat(v):return F(round(v*10**6),10**6)
X9=[(rat((0.93 if i%3==2 else 1)*math.cos(2*math.pi*i/9)),rat((0.93 if i%3==2 else 1)*math.sin(2*math.pi*i/9))) for i in range(9)]
w=is_min_obstruction(X9)
out['source_nine_point']=dict(points=[S(p) for p in X9],minimal_obstruction=w is not None,deletion_centers=[S(c) for c in w] if w else None)
# 3 six-point minimal obstruction refuting three-triangle Helly
X6=[(F(2057,5000),F(9311,10000)),(F(219,625),F(383,400)),(F(437,5000),F(9641,10000)),(F(-2731,5000),F(-1103,1250)),(F(-2367,10000),F(-9911,10000)),(F(147,625),F(-5213,5000))]
w6=is_min_obstruction(X6)
tr=list(combinations(X6,3))
def cells(Ts):
    c=[[]]
    for T in Ts:
        c=[q+H for q in c for H in pieces(T) if feasible(q+H)]
        if not c:return 0
    return len(c)
out['six_point_three_triangle_refutation']=dict(points=[S(p) for p in X6],minimal_obstruction=w6 is not None,deletion_centers=[S(c) for c in w6] if w6 else None,
    all20_intersection_cells=cells(tr),empty_triples=sum(cells([tr[i] for i in s])==0 for s in combinations(range(20),3)))
# 4 triangle pieces (source Lemma 2.2) vs Lemma A
random.seed(7);bad=0;tot=0
for t in range(40):
    T=[(F(random.randint(-20,20)),F(random.randint(-20,20))) for _ in range(3)]
    if (T[1][0]-T[0][0])*(T[2][1]-T[0][1])-(T[1][1]-T[0][1])*(T[2][0]-T[0][0])==0: continue
    L,N=data(T)
    for s in range(40):
        p=(F(random.randint(-60,60),2),F(random.randint(-60,60),2));tot+=1;bad+=inM(T,p)!=admissible(T,p,L,N)
out['lemma22_pieces_vs_lemmaA']=dict(points=tot,mismatches=bad)
# 5 parabola: random finite subsets are c.s.c. (Lemma T4 instance), with exact center
random.seed(5);ok=0;tr5=0
for t in range(30):
    xs=sorted(set(random.randint(-30,30) for _ in range(random.randint(3,9))))
    P=[(F(x),F(x*x)) for x in xs]
    if len(P)<3: continue
    tr5+=1;c=(F(xs[0]+xs[-1],2),F(max(x*x for x in xs)))
    ok+=admissible(P,c,*data(P))
out['parabola_subsets_center_(c,maxY)']=dict(trials=tr5,admissible=ok)
# 6 near-symmetric model vs exact (small sample)
random.seed(5);agree=tot=0
for trial in range(120):
    m=random.choice([3,4]);ang=sorted(random.uniform(0,math.pi) for _ in range(m))
    q=[(F(round(100*math.cos(a))),F(round(100*math.sin(a)))) for a in ang];full=q+[(-x,-y) for x,y in q]
    if len(hull(full))!=2*m: continue
    eps=F(1,10**4);u=[(F(random.randint(-9,9)),F(random.randint(-9,9))) for _ in range(2*m)]
    X=[(full[i][0]+eps*u[i][0],full[i][1]+eps*u[i][1]) for i in range(2*m)]
    if len(hull(X))!=2*m: continue
    ws=[((u[j][0]+u[j+m][0])/2,(u[j][1]+u[j+m][1])/2) for j in range(m)]
    ext=[(-q[-1][0],-q[-1][1])]+q+[(-q[0][0],-q[0][1])]
    ds=[(ext[i+1][0]-ext[i][0],ext[i+1][1]-ext[i][1]) for i in range(m+1)]
    tot+=1;agree+=(model.feasible(ws,ds,range(m)) is not None)==(center(X) is not None)
out['near_symmetric_model_vs_exact']=dict(instances=tot,agree=agree)
json.dump(out,open('exact-checks.json','w'),indent=1)
print(json.dumps({k:{kk:vv for kk,vv in v.items() if kk not in('points','deletion_centers')} for k,v in out.items()},indent=1))
