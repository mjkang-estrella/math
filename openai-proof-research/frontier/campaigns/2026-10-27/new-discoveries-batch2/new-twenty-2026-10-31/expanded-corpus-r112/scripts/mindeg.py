"""SAT: does a graph G on cyclically ordered Z_n exist with no clockwise (cyclic monotone) path of b vertices and min degree >= d?
(374241 in complement form: red degree <= a-2 <=> blue min degree >= n-1-(a-2).) usage: mindeg.py n b d out.cnf"""
import sys,itertools
n,b,d,out=map(int,sys.argv[1:4])+[sys.argv[4]] if False else (int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4])
def x(u,v):
    if u>v:u,v=v,u
    return u*n-u*(u+1)//2+(v-u-1)+1
nv=n*(n-1)//2; cl=[]
for c in itertools.combinations(range(n),b):
    for t in range(b):
        r=c[t:]+c[:t]; cl.append([-x(r[i],r[i+1]) for i in range(b-1)])
# at most (n-1-d) non-edges at each vertex: sequential counter on negated literals
def atmost(lits,k):
    global nv
    if k>=len(lits): return
    if k==0:
        for l in lits: cl.append([-l]); 
        return
    s=[[0]*(k+1) for _ in lits]
    for i in range(len(lits)):
        for j in range(1,k+1): nv+=1; s[i][j]=nv
    for i,l in enumerate(lits):
        cl.append([-l,s[i][1]])
        if i>0:
            for j in range(1,k+1): cl.append([-s[i-1][j],s[i][j]])
            for j in range(2,k+1): cl.append([-l,-s[i-1][j-1],s[i][j]])
            cl.append([-l,-s[i-1][k]])
for v in range(n):
    atmost([-x(v,u) for u in range(n) if u!=v], n-1-d)
with open(out,'w') as f:
    f.write(f'p cnf {nv} {len(cl)}\n')
    for c in cl: f.write(' '.join(map(str,c))+' 0\n')
