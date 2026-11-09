# Controls for bressoud366890.py: proven cases k=2..4 (Theorem 1.7), a perturbed variant (alpha without factor 2) must fail, larger bound B gives same LHS, and extended n for k=5.
import sys,time; sys.path.insert(0,sys.argv[1]+'/scripts/misc')
import importlib.util
spec=importlib.util.spec_from_file_location('b',sys.argv[1]+'/scripts/misc/bressoud366890.py')
src=open(sys.argv[1]+'/scripts/misc/bressoud366890.py').read().split('t0=time.time()')[0]
ns={}; exec(src,ns)
lhs,rhs=ns['lhs'],ns['rhs']
print('proven k=2..4:',all(lhs(n,k,i,2*n+2)==rhs(n,k,i) for k in (2,3,4) for i in range(1,k+1) for n in range(0,7)))
print('bound robustness k=5:',all(lhs(n,5,i,2*n+2)==lhs(n,5,i,3*n+5) for i in range(1,5) for n in range(0,5)))
src2=src.replace('top=2*n-2*sum(ns[:j-1])-ns[j-1]-ns[j]-2*a','top=2*n-2*sum(ns[:j-1])-ns[j-1]-ns[j]-a'); ns2={}; exec(src2,ns2)
print('perturbed (alpha not doubled) k=5 mismatches:',sum(ns2['lhs'](n,5,i,2*n+2)!=ns2['rhs'](n,5,i) for i in range(1,5) for n in range(0,7)))
t0=time.time(); ok=True; last=None
for n in range(9,16):
    for i in range(1,5):
        if time.time()-t0>80: break
        ok&= lhs(n,5,i,2*n+2)==rhs(n,5,i); last=(n,i)
print('k=5 extended through (n,i)=',last,'all equal',ok)
