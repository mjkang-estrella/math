from pathlib import Path
from fractions import Fraction as Q
from math import factorial
N=12
c=[1]
for n in range(1,N+1): c.append(c[-1]+c[n//2])
def mul(a,b):
 out=[Q(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def expr(a):return ' + '.join(f'({int(x)})*(m:ℤ)^{i}' for i,x in enumerate(a) if x) or '0'
# Formal binomial theorem expansion, then independently checked by induction in Lean.
cs=[]
for n in range(N+1):
 poly=[Q(0)]*(n+1);power=[1]+[0]*N;fall=[Q(1)]
 for k in range(n+1):
  for j,b in enumerate(fall):poly[j]+=Q(power[n],factorial(k))*b
  power=[sum(power[i]*([0]+c[1:])[j-i] for i in range(j+1)) for j in range(N+1)]
  fall=mul(fall,[-k,1])
 cs.append([v*factorial(n) for v in poly]);assert all(v.denominator==1 for v in cs[-1])
s='''import UlasOdd5Coefficients
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open PowerSeries
namespace Ulas.Round5Odd
'''
for n in range(N+1):
 if n == 0:
  s+="theorem power_coeff_0 (m : ℕ) : 1*coeff 0 (C^m) = 1 := by simp\n"
  continue
 s+=f'''theorem power_coeff_{n} (m : ℕ) : {factorial(n)}*coeff {n} (C^m) = {expr(cs[n])} := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      {', '.join('C_coeff_'+str(i) for i in range(n+1))}]
    linear_combination ih''' + ''.join(f' + {factorial(n)//factorial(i)*c[n-i]}*(power_coeff_{i} m)' for i in range(1,n))+ '\n'
s+='end Ulas.Round5Odd\n';Path('src/UlasOdd5PowerCoefficients.lean').write_text(s)
# Save exact integer numerator arrays to permit readout generator reuse.
import json
Path('tmp/power-numerators.json').write_text(json.dumps([[int(x) for x in a] for a in cs]))
