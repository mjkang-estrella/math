from pathlib import Path
from fractions import Fraction
import mpmath as mp,json
mp.mp.dps=70
p=Path(__file__).resolve().parent
rows=[]
for vv,ww in [('1','1'),('.2','3'),('4','.03'),('.125','.375'),('7','2')]:
    v,w=mp.mpf(vv),mp.mpf(ww);s=v+w;theta=mp.atan(mp.sqrt(w/v))
    for tt in ['0','.03','.4','2','9']:
        t=mp.mpf(tt)
        exact=mp.exp(-s*t)*(1+mp.erfi(mp.sqrt(v*t))*mp.erfi(mp.sqrt(w*t)))
        polar=2/mp.pi*(mp.quad(lambda z:mp.exp(-t*(s-v/mp.cos(z)**2)),[0,theta])+mp.quad(lambda z:mp.exp(-t*(s-w/mp.sin(z)**2)),[theta,mp.pi/2]))
        error=abs(exact-polar);assert error<mp.mpf('1e-60'),(vv,ww,tt,error)
        rows.append({'v':vv,'w':ww,'t':tt,'K':mp.nstr(exact,35),'angular_error':mp.nstr(error,5)})
mom=[]
for pp,qq in [(1,2),(1,3),(2,3),(3,4),(2,5),(5,7)]:
    beta=mp.mpf(pp)/qq
    for ss in ['0','.5','1','2','3.5','8']:
        s=mp.mpf(ss);z=(mp.mpf(qq)/mp.mpf(pp)**beta)**s
        for j in range(1,qq+1):z*=mp.gamma(mp.mpf(j)/qq+s/qq)/mp.gamma(mp.mpf(j)/qq)
        for j in range(1,pp+1):z/=mp.gamma(mp.mpf(j)/pp+s/qq)/mp.gamma(mp.mpf(j)/pp)
        target=mp.gamma(1+s)/mp.gamma(1+beta*s);err=abs(z/target-1);assert err<mp.mpf('1e-60')
        mom.append({'p':pp,'q':qq,'s':ss,'relative_error':mp.nstr(err,5)})
def ml(a,b,z):
    return mp.nsum(lambda n:z**n/mp.gamma(a*n+b),[0,mp.inf])
series=[]
for aa in ['.125','.2','.3','.4','.5']:
    a=mp.mpf(aa)
    for tt in ['.02','.3','1.1']:
        t=mp.mpf(tt);lhs=ml(2*a,1,-t)**2+t*ml(2*a,1+a,-t)**2;rhs=abs(ml(a,1,1j*mp.sqrt(t)))**2
        err=abs(lhs-rhs);assert err<mp.mpf('1e-50'),(aa,tt,err)
        series.append({'a':aa,'t':tt,'f':mp.nstr(lhs,35),'error':mp.nstr(err,5)})
coeff=[]
for aa in ['.125','.2','.3','.4','.5']:
    a=mp.mpf(aa)
    for k in range(11):
        bk=sum((-1)**j/(mp.gamma(a*j+1)*mp.gamma(a*(2*k-j)+1)) for j in range(2*k+1));assert bk>0
        coeff.append({'a':aa,'k':k,'alternating_coefficient':mp.nstr(bk,30)})
result={'status':'PASS numerical diagnostics only, not proof','dps':mp.mp.dps,'angular':rows,'gamma_moments':mom,'series_even_odd':series,'alternating_taylor':coeff}
(p/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS25angular identities,36finite gamma-moment identities,15even/odd identities,55positive alternating coefficients; diagnostics not proofs')
