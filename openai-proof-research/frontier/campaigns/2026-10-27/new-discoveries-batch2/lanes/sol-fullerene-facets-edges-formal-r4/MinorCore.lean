import RealCore
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TripleCertificates
open FullereneGeometry
def coord (v : V) (j : Fin 3) : ℤ := ![v.x,v.y,v.z] j
def minorCert (a b c : Point) (j k : Fin 3) : ℤ :=
 (coord b.num j*a.den-coord a.num j*b.den)*
 (coord c.num k*a.den-coord a.num k*c.den)-
 (coord b.num k*a.den-coord a.num k*b.den)*
 (coord c.num j*a.den-coord a.num j*c.den)
theorem rv_coord (v : V) (j : Fin 3) : rv v j = (coord v j : ℤ) := by
 fin_cases j <;> rfl
theorem minor_real (a b c : Point) (ha : 0 < a.den) (hb : 0 < b.den)
 (hc : 0 < c.den) (j k : Fin 3) (hm : minorCert a b c j k ≠ 0) :
 (rp b j-rp a j)*(rp c k-rp a k)-(rp b k-rp a k)*(rp c j-rp a j) ≠ 0 := by
 have ha' : (a.den:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
 have hb' : (b.den:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
 have hc' : (c.den:ℝ) ≠ 0 := by exact_mod_cast hc.ne'
 have he : ((rp b j-rp a j)*(rp c k-rp a k)-(rp b k-rp a k)*(rp c j-rp a j)) *
   ((a.den:ℝ)^2*b.den*c.den) = (minorCert a b c j k:ℤ) := by
  simp only [rp,rv_coord,minorCert,Int.cast_sub,Int.cast_mul]
  field_simp
 intro hz
 rw [hz,zero_mul] at he
 exact (by exact_mod_cast hm : (minorCert a b c j k:ℝ) ≠ 0) he.symm
end TripleCertificates
