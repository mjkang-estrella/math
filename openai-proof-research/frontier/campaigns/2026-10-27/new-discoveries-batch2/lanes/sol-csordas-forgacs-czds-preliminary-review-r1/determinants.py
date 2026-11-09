from pathlib import Path
from math import comb,lcm
from fractions import Fraction as Q
import json
L=Path(__file__).parent
def det(A):
 n=len(A);den=lcm(*(x.denominator for row in A for x in row))
 a=[[int(x*den) for x in row] for row in A];prev=1;sw=1
 for k in range(n-1):
  if not a[k][k]:
   j=next(j for j in range(k+1,n) if a[j][k]);a[k],a[j]=a[j],a[k];sw=-sw
  p=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    x=a[i][j]*p-a[i][k]*a[k][j];assert x%prev==0;a[i][j]=x//prev
  for i in range(k+1,n):a[i][k]=0
  prev=p
 return Q(sw*a[-1][-1],den**n)
old=det([[Q(1,(i+j)**2+i+j+1) for j in range(4)] for i in range(4)])
new=det([[Q(comb(i+j,i),(i+j)**2+i+j+1) for j in range(37)] for i in range(37)])
assert old==Q(-55936,2833723113403) and new<0
out={'method':'fraction-free integer Bareiss with exact divisibility, no LDL', 'old_Example_1_8_verified':True,'new_scaled_Hankel_dimension':37,'new_determinant_negative':new<0,'new_determinant_numerator_hex':hex(new.numerator),'new_determinant_denominator_hex':hex(new.denominator)}
(L/'determinant-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if not k.endswith('_hex')})
