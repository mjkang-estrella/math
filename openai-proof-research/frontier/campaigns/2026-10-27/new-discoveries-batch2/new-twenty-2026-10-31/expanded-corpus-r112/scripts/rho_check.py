# Validate rho^w = y D_y/(x D_x) at dominant singularity, D = 1 - x(1+y) + 1/B(1/x,1/y) (source Fact 2.9), against brute-force counts.
import itertools,sys
from fractions import Fraction
def borders(w):
    return [w[:j] for j in range(1,len(w)+1) if w[:j]==w[len(w)-j:]]
def rho_formula(w):
    B=borders(w)
    import mpmath as mp
    mp.mp.dps=40
    C=lambda x,y: sum(x**(-len(b))*y**(-b.count('1')) for b in B)
    D=lambda x,y: 1-x*(1+y)+1/C(x,y)
    x0=mp.findroot(lambda x: D(x,1), 0.6)
    # choose smallest positive root: scan
    xs=[mp.findroot(lambda x: D(x,1), s) for s in [0.5,0.55,0.6,0.7]]
    x0=min([x for x in xs if x>0.4])
    Dx=mp.diff(lambda x: D(x,1),x0); Dy=mp.diff(lambda y: D(x0,y),1)
    return Dy/(x0*Dx)
def rho_brute(w,n):
    tot=0;cnt=0
    for t in itertools.product('01',repeat=n):
        s=''.join(t)
        if w in s: continue
        cnt+=1;tot+=s.count('1')
    return tot/(n*cnt)
for w in ['11','1001','1100','1010','110']:
    print(w, rho_formula(w), rho_brute(w,18))
