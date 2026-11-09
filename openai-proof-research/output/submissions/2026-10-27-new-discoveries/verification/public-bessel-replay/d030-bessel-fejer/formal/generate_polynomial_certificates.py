from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
N=20
p=[Q((-1)**k,factorial(k)**2) for k in range(N)]
h=[Q((-1)**k,factorial(k)*factorial(k+1)) for k in range(N)]
def bern(co,a,b):
 d=len(co)-1
 c=[sum(co[j]*comb(j,k)*a**(j-k)*(b-a)**k for j in range(k,d+1)) for k in range(d+1)]
 return [sum(c[k]*Q(comb(i,k),comb(d,k)) for k in range(i+1)) for i in range(d+1)]
def lit(q):return f'({q.numerator} / {q.denominator})'
configs=[('h0','hterm',h,Q(0),Q(9,4),Q(1,5),True),('pNeg','term',p,Q(9,4),Q(552,100)**2/4,-Q(1,50000),False),('h2','hterm',h,Q(552,100)**2/4,Q(55201,10000)**2/4,-Q(3,25),False)]
s='''import BernsteinBounds
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators unitInterval
namespace BesselFejer
'''
for name,tm,co,a,b,bound,lower in configs:
 cs=bern(co,a,b)
 for suffix,vec in [('Coefficients',cs),('Scaled',[c*comb(19,i) for i,c in enumerate(cs)])]:
  s+=f'\ndef {name}{suffix} : Fin 20 → ℚ :=\n  !['+',\n    '.join(lit(c) for c in vec)+']\n'
 rel=f'{lit(bound)} ≤ {name}Coefficients i' if lower else f'{name}Coefficients i ≤ {lit(bound)}'
 s+=f'\nlemma {name}Coefficients_bound : ∀ i, {rel} := by\n  decide +kernel\n'
 s+=f'''\nlemma {name}Scaled_eq : ∀ i, {name}Scaled i = {name}Coefficients i * (Nat.choose 19 (i : ℕ) : ℚ) := by
  decide +kernel

lemma {name}_transform (t : unitInterval) :
    (∑ n ∈ Finset.range 20, {tm} n ({lit(a)} + {lit(b-a)} * (t : ℝ))) =
      bernsteinSum {name}Coefficients t := by
  rw [bernsteinSum_scaled {name}Coefficients {name}Scaled {name}Scaled_eq]
  norm_num [{name}Scaled, {tm}, Finset.sum_range_succ, Fin.sum_univ_succ, Nat.factorial]
  ring

lemma {name}_bound (q : ℝ) (hqa : {lit(a)} ≤ q) (hqb : q ≤ {lit(b)}) :
    {'(' + lit(bound) + ' : ℝ) ≤' if lower else ''}
    (∑ n ∈ Finset.range 20, {tm} n q)
    {'' if lower else '≤ (' + lit(bound) + ' : ℝ)'} := by
  have hab : (0 : ℝ) < {lit(b-a)} := by norm_num
  let t : unitInterval := ⟨(q-{lit(a)}) / {lit(b-a)}, by
    constructor
    · exact div_nonneg (by linarith) (le_of_lt hab)
    · apply (div_le_one hab).mpr
      linarith⟩
  have hh := bernsteinSum_{'lower' if lower else 'upper'} {name}Coefficients {lit(bound)}
    {name}Coefficients_bound t
  rw [← {name}_transform] at hh
  have he : {lit(a)} + {lit(b-a)} * (t : ℝ) = q := by
    dsimp [t]
    field_simp
    ring
  rw [he] at hh
  norm_num at hh ⊢
  exact hh
'''
s+='\nend BesselFejer\n'
Path('PolynomialCertificates.lean').write_text(s)
print('generated',len(s),'bytes')
