from pathlib import Path
from fractions import Fraction as F
import json,hashlib,datetime
P=Path(__file__).resolve().parent
results={}
# Piecewise constant cube jitter: exact midpoint failure away from cell boundaries.
# p(-1),p(0),p(1)=1/4,1/2,1/4, half-open centered unit cells.
x,y=F(49,100),F(53,100);mid=(x+y)/2
val=lambda t: F(1,2) if F(-1,2)<t<F(1,2) else F(1,4)
a,b,c=val(x),val(y),val(mid)
assert c*c<a*b
results['jitter_midpoint']={'x':str(x),'y':str(y),'mid':str(mid),'fx':str(a),'fy':str(b),'fmid':str(c),'fmid_squared':str(c*c),'fx_fy':str(a*b)}
# Uniform L1 lattice balls: full exact finite enumeration, no numerical eigensolver.
rows=[]
for m in [1,2,3,4,8,16,32,64]:
 pts=[(x,y) for x in range(-m,m+1) for y in range(-m,m+1) if abs(x)+abs(y)<=m]
 N=len(pts); assert N==2*m*m+2*m+1
 cov=F(sum(x*x for x,y in pts),N);cy=F(sum(y*y for x,y in pts),N)
 assert sum(x*y for x,y in pts)==0 and cov==cy
 formula=F(m*(m+1)*(m*m+m+1),3*N);assert formula==cov
 continuous=F(m*m,6);err=cov-continuous
 # Exact algebra: discrepancy positive and at most (m+1)/6.
 assert err==F(m*(2*m*m+3*m+2),6*N)
 assert 0<err<=F(m+1,6)
 rows.append({'m':m,'N':N,'discrete_cov_diagonal':str(cov),'continuous_cov_diagonal':str(continuous),'error':str(err)})
results['diamonds']=rows
# Smoothing changes exact lattice ratios even for a log-concave two-point law.
# With kernel g(0)=a,g(1)=b>0, p=(2/3,1/3), ratio f0/f1=(2a+b)/(a+2b) !=2.
assert F(2+F(1,2),1+2*F(1,2))!=2
results['smoothing_objection']='(2a+b)-2(a+2b)=-3b !=0 for b>0'
heads={}
for n in ['omega','openai']:
 raw=(P/'sources'/(n+'-head')).read_bytes();obj=json.loads(raw)
 heads[n]={'sha':obj['sha'],'date':obj['commit']['committer']['date'],'retrieved_response_sha256':hashlib.sha256(raw).hexdigest()}
results['current_heads']=heads
results['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(P/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
