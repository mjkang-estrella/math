from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json,sys,hashlib,time
sys.set_int_max_str_digits(100000)
D=50;N=949;x=Q(523,527)
start=time.time()
c=[Q(comb(2*k,k),4**k) for k in range(N+1)]
a=[Q(1)]
for j in range(1,N//D+1):a.append(a[-1]*Q(2*j-3,2*j))
b=[sum((a[j]*c[k-j*D] for j in range(k//D+1)),Q(0)) for k in range(N+1)]
T=[Q(1),x]
for k in range(2,N+1):T.append(2*x*T[-1]-T[-2])
v=sum((bk*tk for bk,tk in zip(b,T)),Q(0))
print('D',D,'d',D-1,'n',N,'x',x,'value',float(v),'numsign',v.numerator<0,'seconds',time.time()-start,'numdigits',len(str(v.numerator)))
out={'D':D,'d':D-1,'n':N,'cos_t':str(x),'value_numerator':str(v.numerator),'value_denominator':str(v.denominator),'negative':v<0,'coefficient_definition':'b_k=sum_{j=0}^{floor(k/D)} a_j*C(2(k-jD),k-jD)/4^(k-jD), a0=1, a_j=a_(j-1)*(2j-3)/(2j)','t_definition':'t=arccos(523/527)','coefficient_sha256':hashlib.sha256(('\n'.join(map(str,b))+'\n').encode()).hexdigest()}
Path('trig-exact-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
assert v<0
assert all(sum(b[j]*b[k-j] for j in range(k+1))==(1 if k<D else 0) for k in range(N+1))
print('Exact square-identity coefficient check PASS through n',N)
