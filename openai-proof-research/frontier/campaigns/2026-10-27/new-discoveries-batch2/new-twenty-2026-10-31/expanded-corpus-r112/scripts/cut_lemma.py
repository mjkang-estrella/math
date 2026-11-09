"""SAT test of the cut lemma for 374236: find a 2-colouring of K_n (cyclic order) with no cyclic red P_a^mon, no cyclic blue
P_b^mon, such that for EVERY cut s both a linear red monotone path with a-1 vertices and a linear blue one with b-1 vertices exist
in the linear order L_s = (s, s+1, ..., s-1). SAT => lemma fails for (a,b,n). usage: cut_lemma.py a b n out.cnf"""
import sys,itertools
a,b,n,out=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
def x(u,v):
    if u>v:u,v=v,u
    return u*n-u*(u+1)//2+(v-u-1)+1   # TRUE = blue (colour 2)
nv=n*(n-1)//2
cl=[]
def new():
    global nv; nv+=1; return nv
# forbid cyclic red P_a: for every cyclically ordered a-tuple (rotations of sorted subsets), some path edge blue
for k,col in [(a,'r'),(b,'b')]:
    for c in itertools.combinations(range(n),k):
        for t in range(k):
            r=c[t:]+c[:t]
            lits=[x(r[i],r[i+1]) for i in range(k-1)]
            cl.append(lits if col=='r' else [-l for l in lits])
# existence of linear red P_{a-1} and blue P_{b-1} in every L_s
for s in range(n):
    order=[(s+i)%n for i in range(n)]
    for k,col in [(a-1,'r'),(b-1,'b')]:
        # P[v][j]: there is a monochromatic increasing path in L_s with j vertices ending at order[v]
        P=[[None]*(k+1) for _ in range(n)]
        for v in range(n):
            for j in range(2,k+1):
                P[v][j]=new()
                ys=[]
                for u in range(v):
                    y=new(); ys.append(y)
                    e=x(order[u],order[v]); e= -e if col=='r' else e
                    cl.append([-y,e])
                    if j-1>=2: cl.append([-y,P[u][j-1]])
                cl.append([-P[v][j]]+ys)
        cl.append([P[v][k] for v in range(n)] if k>=2 else [])
cl=[c for c in cl if c]
with open(out,'w') as f:
    f.write(f'p cnf {nv} {len(cl)}\n')
    for c in cl: f.write(' '.join(map(str,c))+' 0\n')
print('a',a,'b',b,'n',n,'vars',nv,'clauses',len(cl))
