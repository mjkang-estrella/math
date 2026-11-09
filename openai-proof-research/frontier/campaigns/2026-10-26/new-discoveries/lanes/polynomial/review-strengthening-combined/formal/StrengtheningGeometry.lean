import TaxicabGeometry

open TaxicabGeometry

namespace StrengtheningGeometry

noncomputable section

def A : Point := (3,0)
def B : Point := (0,3)
def C : Point := (-3/2,-3/2)
def P : Point := (0,0)

lemma nondegenerate : area A B C ≠ 0 := by norm_num [area,lineValue,A,B,C]

lemma vertex_sizes : norm1 (A-P)=3 ∧ norm1 (B-P)=3 ∧ norm1 (C-P)=3 := by
  norm_num [norm1,A,B,C,P]

lemma side_distances : sideDistance P B C=1 ∧ sideDistance P C A=1 ∧ sideDistance P A B=3 := by
  norm_num [sideDistance,lineDistance,lineValue,lineScale,A,B,C,P]

lemma equality :
    2*(norm1 (A-P)+norm1 (B-P)+norm1 (C-P)) =
      3*(sideDistance P B C+sideDistance P C A+sideDistance P A B+
        min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) := by
  obtain ⟨ha,hb,hc⟩ := vertex_sizes
  obtain ⟨hra,hrb,hrc⟩ := side_distances
  rw [ha,hb,hc,hra,hrb,hrc]
  norm_num

lemma strictly_interior : P ∈ interior (convexHull ℝ ({A,B,C} : Set Point)) := by
  let S : Set Point := {Q | -1/4<Q.1 ∧ Q.1<1/4 ∧ -1/4<Q.2 ∧ Q.2<1/4}
  have hopen : IsOpen S := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const)))
  have hp : P ∈ S := by norm_num [P,S]
  have hsub : S ⊆ convexHull ℝ ({A,B,C} : Set Point) := by
    intro Q hQ
    change -1/4<Q.1 ∧ Q.1<1/4 ∧ -1/4<Q.2 ∧ Q.2<1/4 at hQ
    apply mem_convexHull_of_exists_fintype
      (![(3+3*Q.1-Q.2)/12,(3-Q.1+3*Q.2)/12,(3-Q.1-Q.2)/6] : Fin 3 → ℝ)
      (![A,B,C] : Fin 3 → Point)
    · intro i
      fin_cases i
      · change 0≤(3+3*Q.1-Q.2)/12
        linarith [hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2]
      · change 0≤(3-Q.1+3*Q.2)/12
        linarith [hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2]
      · change 0≤(3-Q.1-Q.2)/6
        linarith [hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2]
    · simp [Fin.sum_univ_succ]
      ring
    · intro i
      fin_cases i <;> simp
    · ext <;> simp [Fin.sum_univ_succ,A,B,C]
      <;> ring
  exact interior_mono hsub (by rw [hopen.interior_eq];exact hp)

#print axioms strictly_interior
#print axioms equality
end
end StrengtheningGeometry
