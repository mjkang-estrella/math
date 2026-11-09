"""Independent small free-cover and class-two group diagnostics; not proof."""
from itertools import product
from fractions import Fraction
from pathlib import Path
import json
L=Path(__file__).resolve().parent
F=list(product(range(2),repeat=3));A=list(product(range(2),repeat=2))
images=[(1,0),(0,1),(1,1)]
def p(x):return tuple(sum(x[i]*images[i][j] for i in range(3))%2 for j in range(2))
def b(x,y):return (x[0]*y[1]-x[1]*y[0])%2
def f(x,y):return sum(x[i]*y[j]*b(images[i],images[j]) for i in range(3) for j in range(i+1,3))%2
assert all(sum(p(x)==a for x in F)==2 for a in A)
assert all((f(x,y)-f(y,x))%2==b(p(x),p(y)) for x,y in product(F,repeat=2))
assert Fraction(sum(f(x,y)==f(y,x) for x,y in product(F,repeat=2)),64)==Fraction(5,8)
D=list(product(range(4),range(2)))
def dmul(a,b):return ((a[0]+(-1)**a[1]*b[0])%4,(a[1]+b[1])%2)
assert Fraction(sum(dmul(a,b)==dmul(b,a) for a,b in product(D,repeat=2)),64)==Fraction(5,8)
assert b((1,0),(0,1))==1 and (2*b((1,0),(0,1)))%2==0
out={'status':'PASS','free_cover_fiber_size':2,'cover_pairs':64,'D8_cp':'5/8','free_cover_cp':'5/8','half_bracket_obstruction_verified':True,'scope':'independent bounded diagnostics'}
(L/'independent-checks.json').write_text(json.dumps(out,indent=2));print(out)
