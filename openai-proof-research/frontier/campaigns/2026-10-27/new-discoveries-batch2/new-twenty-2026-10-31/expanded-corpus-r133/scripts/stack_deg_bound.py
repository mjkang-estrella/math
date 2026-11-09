import sys, math, runpy
sys.argv=['x','0','float']
ns=runpy.run_path(sys.path[0]+'/stack_deg_dp.py' if False else 'scripts/stack_deg_dp.py')
I=ns['I']
N=int(sys.stdin.readline() or 120) if False else 130
for n in range(2,N+1):
    d=I(1,1,n-1)
    lb=(d/n**2)**(1/n)   # source Theorem 2.5: lim = sup_{n>=8} (d_{n-1}/n^2)^{1/n}
    lb2=(d/(4*n))**(1/n) # doubling variant, a=n-1
    if n%5==0 or lb>1.73: print(n, d, I(1,1,n)/d if n<N else None, lb, lb2, flush=True)
    if lb>1.735: break
