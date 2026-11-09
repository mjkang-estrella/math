from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib,json,sys
sys.set_int_max_str_digits(100000)
D=50;N=949;p=523;q=527;R=4*q
c=[Q(comb(2*k,k),4**k) for k in range(N+1)]
a=[Q(1)]
for j in range(1,N//D+1):a.append(a[-1]*Q(2*j-3,2*j))
B=[]
for k in range(N+1):
 v=sum((a[j]*c[k-j*D] for j in range(k//D+1)),Q(0))*4**k
 assert v.denominator==1
 B.append(v.numerator)
for k in range(1,N+1):
 assert 2*k*B[k]==4*(2*k-1)*B[k-1]+(4**D*(2*k-3*D)*B[k-D] if k>=D else 0)-(4**(D+1)*(2*k-3*D-1)*B[k-D-1] if k>=D+1 else 0)
C=[1,p]
for k in range(2,N+1):C.append(2*p*C[-1]-q*q*C[-2])
H=0
for b,c in zip(B,C):H=R*H+b*c
assert H<0
header='''import Mathlib
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace TrigCertificate

'''
s=header
def tree(vals,lo,hi,indent='  '):
 if hi-lo==1:return str(vals[lo])
 mid=(lo+hi)//2
 return 'if n < '+str(mid)+' then\n'+indent+'  '+tree(vals,lo,mid,indent+'  ')+'\n'+indent+'else\n'+indent+'  '+tree(vals,mid,hi,indent+'  ')
for name,vals in [('B',B),('C',C)]:
 s+='def '+name+' (n : ℕ) : ℤ :=\n  if n < 950 then\n    '+tree(vals,0,950,'    ')+'\n  else 0\n\n'
s+='''def bRecCheck : Bool := (List.range 950).all fun k =>
  if k=0 then decide (B k=1) else decide (
    2*(k:ℤ)*B k = 4*(2*(k:ℤ)-1)*B (k-1) +
      (if 50≤k then (4:ℤ)^50*(2*(k:ℤ)-150)*B (k-50) else 0) -
      (if 51≤k then (4:ℤ)^51*(2*(k:ℤ)-151)*B (k-51) else 0))

def cRecCheck : Bool := (List.range 950).all fun k =>
  if k=0 then decide (C k=1) else if k=1 then decide (C k=523) else
    decide (C k=1046*C (k-1)-277729*C (k-2))

def hornerValue : ℤ := (List.range 950).foldl (fun h k => 2108*h+B k*C k) 0

theorem bRecCheck_ok : bRecCheck=true := by decide

theorem cRecCheck_ok : cRecCheck=true := by decide

theorem hornerValue_neg : hornerValue<0 := by decide

end TrigCertificate
'''
pth=Path('formal/TrigCertificate.lean');pth.write_text(s)
Path('trig-certificate-build.json').write_text(json.dumps({'D':D,'d':D-1,'n':N,'p':p,'q':q,'R':R,'H_negative':H<0,'H_digits':len(str(abs(H))),'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'B_count':len(B),'C_count':len(C)},indent=2)+'\n')
print('bytes',len(s),'Hdigits',len(str(abs(H))))
