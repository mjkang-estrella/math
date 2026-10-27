"""Independent exact check of the already-public elliptic primitive; credit0."""
import sympy as s
x,K,E=s.symbols('x K E')
F=4/(1+x)*K**2-(4+4/(1+x)**2)*K*E+3*E**2
G=(x-1)*(2*K**2-2*(x+2)/(x+1)*K*E+(x+2)/(x+1)*E**2)
dG=s.diff(G,x)+s.diff(G,K)*(E-(1-x**2)*K)/(x*(1-x**2))+s.diff(G,E)*(E-K)/x
assert s.cancel(dG-F)==0
assert s.simplify(G.subs({x:0,K:s.pi/2,E:s.pi/2}))==0
print('PASS: exact primitive identity and lower endpoint; public prior proof, credit0')
