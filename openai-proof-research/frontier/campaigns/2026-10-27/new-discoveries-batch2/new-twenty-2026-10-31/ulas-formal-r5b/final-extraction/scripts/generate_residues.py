from math import comb
from pathlib import Path
P=[ [0,0,-1416,-1456,938,1400,476,56,2], [0,0,2401560,2235024,-2604206,-3127080,-183040,820512,379302,71280,6380,264,4] ]
def expr(cs,x):
 return ' + '.join(f'({a})*{x}^{i}' for i,a in enumerate(cs) if a) or '0'
def subst(cs,q,s):
 return [sum(cs[j]*comb(j,i)*q**i*s**(j-i) for j in range(i,len(cs))) for i in range(len(cs))]
s='''import UlasOdd5One
set_option linter.unusedSimpArgs false
namespace Ulas.Round5Odd
/-- Numerators from the independent review. Their identification with the actual
coefficients 1 and 2 is proved in UlasOdd5LowIdentification. -/
'''
for j,cs in enumerate(P,1): s+=f'def lowNumerator{j} (m : ℤ) : ℤ := {expr(cs,"m")}\n'
for j,cs in enumerate(P,1):
 for q,r,v in [(4,3,7),(16,15,11)]:
  sub=subst(cs,q,r); d=2**v
  assert all(a%d==0 for a in sub)
  s+=f'''theorem numerator{j}_{q}_{r} (t : ℤ) : (2:ℤ)^{v} ∣ lowNumerator{j} ({q}*t+{r}) := by
  refine ⟨{expr([a//d for a in sub],"t")},?_⟩
  unfold lowNumerator{j}
  norm_num
  ring
'''
sub=subst(P[0],16,11); assert sub[0]%256==128 and all(a%256==0 for a in sub[1:]); sub[0]-=128
s+=f'''theorem numerator1_16_11 (t : ℤ) : ∃ z : ℤ, lowNumerator1 (16*t+11) = 256*z+128 := by
  refine ⟨{expr([a//256 for a in sub],"t")},?_⟩
  unfold lowNumerator1
  ring
'''
for j,den in [(1,315),(2,467775)]:
 for q,r,v in [(4,3,7),(16,15,11)]:
  s+=f'''theorem low{j}_residue_{q}_{r} (t a : ℤ)
    (h : {den}*a = lowNumerator{j} ({q}*t+{r})) : (2:ℤ)^{v} ∣ a := by
  have hc : IsCoprime ((2:ℤ)^{v}) {den} := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [h]
  exact numerator{j}_{q}_{r} t
'''
s+='''theorem low1_residue_16_11 (t a : ℤ)
    (h : 315*a = lowNumerator1 (16*t+11)) :
    (2:ℤ)^7 ∣ a ∧ ¬ (2:ℤ)^8 ∣ a := by
  obtain ⟨z,hz⟩ := numerator1_16_11 t
  have hc : IsCoprime ((2:ℤ)^7) 315 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  constructor
  · apply hc.dvd_of_dvd_mul_left
    rw [h,hz]
    exact ⟨2*z+1,by norm_num; ring⟩
  · intro hd
    obtain ⟨b,hb⟩ := hd
    rw [hb] at h
    norm_num at h
    omega
end Ulas.Round5Odd
'''
Path('src/UlasOdd5Residues.lean').write_text(s)
