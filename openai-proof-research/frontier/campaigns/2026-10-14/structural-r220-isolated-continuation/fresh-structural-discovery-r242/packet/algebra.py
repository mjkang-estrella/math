from fractions import Fraction as F
from pathlib import Path
import json,re,math
ROOT=Path(__file__).resolve().parent
p=[F(1),F(0),F(-2),F(0),F(-1,3)]
p1=[(i+1)*p[i+1] for i in range(len(p)-1)]
p2=[(i+1)*p1[i+1] for i in range(len(p1)-1)]
r=[F(0)]*5
for i,c in enumerate(p2):r[i]+=c;r[i+2]+=c
for i,c in enumerate(p1):r[i+1]-=4*c
for i,c in enumerate(p):r[i]+=4*c
assert r==[0]*5
# b^2 is the positive root of t^2+6t-3=0; P(b)=0.
# P(s)=-(s^4+6s^2-3)/3, P'(s)=-4s(1+s^2/3).
assert p==[F(1),0,-2,0,F(-1,3)]
assert p1==[0,-4,0,F(-4,3)]
base=ROOT/'private' if (ROOT/'private').exists() else ROOT/'packet/private'
rows=re.findall(r'^f (\d+) (-?\d+)$',(base/'canonical/build/appendices/tables.tex').read_text(),re.M)
assert len(rows)==34
F0=sum((abs(F(c)) for _,c in rows),F(0))/250000
sigma=F(438907,12000000)/F0
assert F0==F(188476004,15625)
assert sigma==F(438907,144749571072)
assert 3633**2*sigma>=40
assert 3632**2*sigma<40
print(json.dumps({'polynomial_ODE_residual':[str(x) for x in r], 'F0':str(F0),'sigma':str(sigma),'L':3633,'upstream_replay':False},indent=2))
