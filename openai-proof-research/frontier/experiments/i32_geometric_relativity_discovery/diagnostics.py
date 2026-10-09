"""Deterministic exact arithmetic checks; not substitutes for the proofs in the report."""
from fractions import Fraction as F
from pathlib import Path
import json, itertools

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i32_geometric_relativity_discovery'

def rosen_ricci(y, yp, ypp, bp, bpp):
    # beta=0 at the tested point by constant transverse coordinate rescaling.
    g=[[F(0) for _ in range(4)] for _ in range(4)]
    g[0][1]=g[1][0]=F(-1);g[2][2]=g[3][3]=y*y
    gi=[[F(0) for _ in range(4)] for _ in range(4)]
    gi[0][1]=gi[1][0]=F(-1);gi[2][2]=gi[3][3]=1/(y*y)
    dg=[[F(0) for _ in range(4)] for _ in range(4)]
    ddg=[[F(0) for _ in range(4)] for _ in range(4)]
    for i,s in [(2,1),(3,-1)]:
        dg[i][i]=2*y*yp+s*2*y*y*bp
        ddg[i][i]=2*yp*yp+2*y*ypp+s*8*y*yp*bp+4*y*y*bp*bp+s*2*y*y*bpp
    dgi=[[-sum(gi[i][k]*dg[k][l]*gi[l][j] for k in range(4) for l in range(4)) for j in range(4)] for i in range(4)]
    def D(i,j,k):return dg[j][k] if i==1 else F(0)
    def DD(i,j,k):return ddg[j][k] if i==1 else F(0)
    gam=[[[sum(gi[a][h]*(D(i,j,h)+D(j,i,h)-D(h,i,j))/2 for h in range(4)) for j in range(4)] for i in range(4)] for a in range(4)]
    dgam=[[[sum((dgi[a][h]*(D(i,j,h)+D(j,i,h)-D(h,i,j))+gi[a][h]*(DD(i,j,h)+DD(j,i,h)-DD(h,i,j)))/2 for h in range(4)) for j in range(4)] for i in range(4)] for a in range(4)]
    ric=[[sum((dgam[k][i][j] if k==1 else 0)-(dgam[k][i][k] if j==1 else 0)+sum(gam[k][i][j]*gam[l][k][l]-gam[l][i][k]*gam[k][j][l] for l in range(4)) for k in range(4)) for j in range(4)] for i in range(4)]
    expected=[[F(0) for _ in range(4)] for _ in range(4)]
    expected[1][1]=-2*(ypp/y+bp*bp)
    assert ric==expected
    assert gam[2][1][2]-gam[3][1][3]==2*bp

rosen=0
for y,yp,bp,bpp in itertools.product([F(1),F(3,4)],[F(-2),F(0),F(3,7)],[F(-3,5),F(0),F(2)],[F(-1),F(4,9)]):
    for ypp in [F(5,7),-bp*bp*y]:
        rosen_ricci(y,yp,ypp,bp,bpp);rosen+=1

exponents=[]
for p in [F(1001,1000),F(11,10),F(4,3),F(2),F(10)]:
    t=1-1/p;a=b=d=t/4
    markov=p*d;curv=t-d-b;remainder=16*b;stop=b+t-d
    assert min(markov,stop,b)>0 and curv>a and remainder>a
    exponents.append(dict(p=str(p),amplitude=str(a),loop=str(b),cutoff_slack=str(d),exception=str(markov),curvature=str(curv),remainder=str(remainder)))

# Explicit coefficient majorant: P=exp(t**b), P''/P is positive and L1 for t>=1.
# b=1/3 gives h=(t**(-4/3)-2*t**(-5/3))/9 >=0 for t>=8.
for t in [F(8),F(27),F(64),F(125)]:
    s=round(float(t)**(1/3)); assert F(s**3)==t
    h=F(1,9*s**4)-F(2,9*s**5)
    assert h>=0

# RN equality examples at critical points: |K|^2=F(r)^3 eps^2 n^2.
charge=F(1,2);mass=(1+charge*charge)/2;radius=F(2)
lapse=1-2*mass/radius+charge*charge/(radius*radius)
assert lapse>0 and 1-2*mass+charge*charge==0
knorm2=[lapse**3*F(1,100)*n*n for n in [10,100,1000]]
assert knorm2[1]/knorm2[0]==100 and knorm2[2]/knorm2[1]==100

out={'status':'PASS','rosen_exact_jet_checks':rosen,'lp_exponents':exponents,'majorant':'P=exp(t^(1/3)), h=(t^(-4/3)-2t^(-5/3))/9, t>=8','rn_K_squared':[str(x) for x in knorm2],'limits':'Exact arithmetic diagnostics. Universal identities and convergence arguments are proved in the report; no numerical evidence is promoted to a theorem.'}
(OUT/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
