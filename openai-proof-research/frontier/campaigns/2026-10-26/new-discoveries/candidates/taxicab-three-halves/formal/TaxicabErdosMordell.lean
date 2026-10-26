import Scalar
import TaxicabGeometry

open TaxicabGeometry

namespace TaxicabErdosMordell

/-- The sharp taxicab inequality for any nonnegative barycentric point. -/
theorem barycentric_bound (la lb lc : ℝ) (A B C P : Point)
    (hAB : A≠B) (hBC : B≠C) (hCA : C≠A)
    (hla : 0≤la) (hlb : 0≤lb) (hlc : 0≤lc)
    (hsum : la+lb+lc=1) (hP : P=la • A+lb • B+lc • C) :
    3*(sideDistance P B C+sideDistance P C A+sideDistance P A B) ≤
      2*(norm1 (A-P)+norm1 (B-P)+norm1 (C-P)) := by
  obtain ⟨hu,hv,hw,hub,hvc,hwa,hau,hbv,hcw⟩ :=
    triangle_side_bounds la lb lc A B C P hAB hBC hCA hla hlb hlc hsum hP
  exact NewDiscoveries.Taxicab.scalar_weighted
    (norm1_nonneg _) (norm1_nonneg _) (norm1_nonneg _) hu hv hw
    (hub.trans (min_le_left _ _)) (hub.trans (min_le_right _ _))
    (hvc.trans (min_le_left _ _)) (hvc.trans (min_le_right _ _))
    (hwa.trans (min_le_left _ _)) (hwa.trans (min_le_right _ _))
    hla hlb hlc hsum hau hbv hcw

/-- A complete geometric statement over the ordinary closed triangle. -/
theorem convexHull_bound (A B C P : Point)
    (hAB : A≠B) (hBC : B≠C) (hCA : C≠A)
    (hP : P ∈ convexHull ℝ ({A,B,C} : Set Point)) :
    (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B) ≤
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) := by
  classical
  have hPf : P ∈ convexHull ℝ (↑({A,B,C} : Finset Point) : Set Point) := by simpa using hP
  obtain ⟨f,hf,hs,hpoint⟩ := Finset.mem_convexHull'.mp hPf
  have hla : 0≤f A := hf A (by simp)
  have hlb : 0≤f B := hf B (by simp)
  have hlc : 0≤f C := hf C (by simp)
  have hsum : f A+f B+f C=1 := by
    simpa [hAB,hBC,hCA,Ne.symm hAB,Ne.symm hBC,Ne.symm hCA,add_assoc] using hs
  have hcomb : P=f A • A+f B • B+f C • C := by
    simpa [hAB,hBC,hCA,Ne.symm hAB,Ne.symm hBC,Ne.symm hCA,add_assoc] using hpoint.symm
  have h := barycentric_bound (f A) (f B) (f C) A B C P hAB hBC hCA hla hlb hlc hsum hcomb
  linarith

/-- The exact arbitrary-triangle interior assertion of MathDB341671. -/
theorem source_conjecture_341671 (A B C P : Point)
    (harea : area A B C≠0)
    (hP : P ∈ interior (convexHull ℝ ({A,B,C} : Set Point))) :
    (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B) ≤
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) := by
  obtain ⟨hAB,hBC,hCA⟩ := area_distinct A B C harea
  exact convexHull_bound A B C P hAB hBC hCA (interior_subset hP)

def sharpA : Point := (0,1)
def sharpB : Point := (-1,0)
def sharpC : Point := (1,0)
def sharpP (e : ℝ) : Point := (0,e)

lemma sharp_triangle_area : area sharpA sharpB sharpC ≠ 0 := by
  norm_num [area,lineValue,sharpA,sharpB,sharpC]

lemma sharp_vertex_sum {e : ℝ} (he : 0≤e) (he1 : e≤1) :
    norm1 (sharpA-sharpP e)+norm1 (sharpB-sharpP e)+norm1 (sharpC-sharpP e)=3+e := by
  simp [norm1,sharpA,sharpB,sharpC,sharpP,abs_of_nonneg he,abs_of_nonneg (sub_nonneg.mpr he1)]
  ring

lemma sharp_side_sum {e : ℝ} (he : 0≤e) (he1 : e≤1) :
    sideDistance (sharpP e) sharpB sharpC+sideDistance (sharpP e) sharpC sharpA+
      sideDistance (sharpP e) sharpA sharpB=2-e := by
  simp [sideDistance,lineDistance,lineValue,lineScale,sharpA,sharpB,sharpC,sharpP,
    abs_of_nonneg he]
  simp only [abs_of_nonneg (show 0≤ -e+1 by linarith)]
  ring

lemma sharp_interior {e : ℝ} (he : 0<e) (he1 : e<1) :
    sharpP e ∈ interior (convexHull ℝ ({sharpA,sharpB,sharpC} : Set Point)) := by
  let S : Set Point := {Q | 0<Q.2 ∧ Q.2+|Q.1|<1}
  have hopen : IsOpen S := by
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_snd.add continuous_fst.abs) continuous_const)
  have hPS : sharpP e ∈ S := by simpa [S,sharpP] using And.intro he he1
  have hsub : S ⊆ convexHull ℝ ({sharpA,sharpB,sharpC} : Set Point) := by
    intro Q hQ
    change 0<Q.2 ∧ Q.2+|Q.1|<1 at hQ
    apply mem_convexHull_of_exists_fintype
      (![Q.2,(1-Q.2-Q.1)/2,(1-Q.2+Q.1)/2] : Fin 3 → ℝ)
      (![sharpA,sharpB,sharpC] : Fin 3 → Point)
    · intro i
      fin_cases i
      · change 0≤Q.2
        exact hQ.1.le
      · change 0≤(1-Q.2-Q.1)/2
        linarith [le_abs_self Q.1]
      · change 0≤(1-Q.2+Q.1)/2
        linarith [neg_abs_le Q.1]
    · simp [Fin.sum_univ_succ]
      ring
    · intro i
      fin_cases i <;> simp
    · ext <;> simp [Fin.sum_univ_succ,sharpA,sharpB,sharpC]
      ring
  exact interior_mono hsub (by rw [hopen.interior_eq]; exact hPS)

/-- No coefficient greater than3/2 works for every strictly interior taxicab point. -/
theorem coefficient_sharp {K : ℝ} (hK : (3/2:ℝ)<K) :
    ∃ P : Point, P ∈ interior (convexHull ℝ ({sharpA,sharpB,sharpC} : Set Point)) ∧
      norm1 (sharpA-P)+norm1 (sharpB-P)+norm1 (sharpC-P) <
        K*(sideDistance P sharpB sharpC+sideDistance P sharpC sharpA+
          sideDistance P sharpA sharpB) := by
  have hK1 : 0<K+1 := by linarith
  have hratio : 0<(2*K-3)/(K+1) := div_pos (by linarith) hK1
  obtain ⟨e,he,hebound⟩ := exists_between (lt_min (show (0:ℝ)<1 by norm_num) hratio)
  have he1 : e<1 := lt_of_lt_of_le hebound (min_le_left _ _)
  have heratio : e<(2*K-3)/(K+1) := lt_of_lt_of_le hebound (min_le_right _ _)
  have hecross := (lt_div_iff₀ hK1).mp heratio
  refine ⟨sharpP e,sharp_interior he he1,?_⟩
  rw [sharp_vertex_sum he.le he1.le,sharp_side_sum he.le he1.le]
  nlinarith

#print axioms source_conjecture_341671
#print axioms coefficient_sharp
end TaxicabErdosMordell
