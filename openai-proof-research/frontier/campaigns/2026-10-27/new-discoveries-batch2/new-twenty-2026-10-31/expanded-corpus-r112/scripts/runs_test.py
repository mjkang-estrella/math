"""374236 transfer test: coloring of K_n (cyclic) with no red cyclic P_a^mon, no blue cyclic P_b^mon, and vertex 0 having
red forward run 1..rf and red backward run n-1..n-rb (rf+rb = a-1), i.e. J(0)+K(0) >= a+1. usage: runs_test.py a b n rf out"""
import sys,itertools
a,b,n,rf,out=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
rb=a-1-rf
def x(u,v):
    if u>v:u,v=v,u
    return u*n-u*(u+1)//2+(v-u-1)+1
cl=[]
for k,col in [(a,'r'),(b,'b')]:
    for c in itertools.combinations(range(n),k):
        for t in range(k):
            r=c[t:]+c[:t]; lits=[x(r[i],r[i+1]) for i in range(k-1)]
            cl.append(lits if col=='r' else [-l for l in lits])
for i in range(1,rf+1): cl.append([-x(0,i)])
for j in range(1,rb+1): cl.append([-x(0,n-j)])
with open(out,'w') as f:
    f.write(f'p cnf {n*(n-1)//2} {len(cl)}\n')
    for c in cl: f.write(' '.join(map(str,c))+' 0\n')
