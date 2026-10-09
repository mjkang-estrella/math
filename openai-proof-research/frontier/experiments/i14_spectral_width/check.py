"""Exact algebra diagnostics; not a proof of geometric gluing or novelty."""
from fractions import Fraction as F
from pathlib import Path
import json,itertools
counts={'surface_square_identity':0,'collar_identity':0,'warped_endpoint_coefficients':0}
for beta in [F(1),F(4,5),F(3,4),F(7,10),F(201,300)]:
 gamma=2-1/beta;c=(3*beta-2)/(2*beta-1)
 assert F(1,2)<gamma<=1 and c>0
 assert gamma/(2*gamma-1)==1/c
 for T,p,v,mu in itertools.product([F(-2),F(-1,3),F(0),F(1,2),F(3)],repeat=4):
  left=(beta-gamma)*T*T+2*(gamma-1)*T*p+(2-gamma)*p*p+mu*mu+(beta-1)*v*v+(mu+v)**2/2
  right=(p+(beta-1)*T)**2/beta+(beta-F(1,2))*(v+mu/(2*beta-1))**2+c*mu*mu
  assert left==right
  counts['surface_square_identity']+=1
 for H,mp,ap,aq in itertools.product([F(-2),F(0),F(1,3)],repeat=4):
  # Collar normal terms before and after m'=H-T'; remove -2m''.
  Tp=H-mp
  left=-(ap*ap+aq*aq)-H*H+2*H*Tp-beta*Tp*Tp
  right=-(ap*ap+aq*aq)-mp*mp+(1-beta)*(H-mp)**2
  assert left==right
  counts['collar_identity']+=1
 # Negative quadratic trace coefficient at the seam, under H=ap+aq.
 for ap,aq in itertools.product([F(-2),F(0),F(1,3)],repeat=2):
  H=ap+aq
  assert -(ap*ap+aq*aq)+(1-beta)*H*H <= 0
# General n=m+1 warped metric, h=(log f)' arbitrary:
# Scal=-2m h'-m(m+1)h^2; Delta(f^-m/2)/(f^-m/2)=-m h'/2-m^2 h^2/4.
for m in range(2,101):
 a=F(4*(m+1),m)
 assert a*m/2-2*m==2
 assert a*m*m/4-m*(m+1)==0
 counts['warped_endpoint_coefficients']+=1
out={'status':'PASS','counts':counts,'limitation':'Exact finite diagnostics only; universal squares and geometric steps require written proof review.'}
p=Path(__file__).with_name('results.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
