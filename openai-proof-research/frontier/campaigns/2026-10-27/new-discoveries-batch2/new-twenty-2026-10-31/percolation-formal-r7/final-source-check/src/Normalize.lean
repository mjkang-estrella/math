import CollineationFamily
import Noncollinear
import PG5CNF
namespace Percolation
set_option autoImplicit false

def normalizedUnits5 : List (CNF.Clause SatVar) :=
  [[(.a 0,false)],[(.a 25,false)],[(.a 30,false)]]
def normalizedCNF5 : List (CNF.Clause SatVar) := inputCNF5 ++ normalizedUnits5

theorem normalize_witness5 (a : Infection 5) (hm : Minimal PG5 5 a)
    (ht : TimeIs PG5 5 a 2) : ∃ b : Infection 5,
    Minimal PG5 5 b ∧ TimeIs PG5 5 b 2 ∧ b 0 = true ∧ b 25 = true ∧ b 30 = true := by
  obtain ⟨p,q,r,hp,hq,hr,hn⟩ := percolates_noncollinear5 a hm.1
  let f := familyF p
  have hf : f.p 0 = p := familyF_spec p
  have hfp : f.pinv p = 0 := by rw [← hf, f.pi]
  have hnc := noncollinear_pull5 f p q r hn
  rw [hfp] at hnc
  have hq0 : f.pinv q ≠ 0 := Ne.symm (noncollinear_ne5 0 (f.pinv q) (f.pinv r) hnc)
  let g := familyG (f.pinv q)
  obtain ⟨hg0,hgq⟩ := familyG_spec (f.pinv q) hq0
  have hgp : g.pinv 0 = 0 := (congrArg g.pinv hg0.symm).trans (g.pi 0)
  have hg25 : g.pinv (f.pinv q) = 25 := by rw [← hgq, g.pi]
  have hnc2 := noncollinear_pull5 g 0 (f.pinv q) (f.pinv r) hnc
  rw [hgp,hg25] at hnc2
  let k := familyH (g.pinv (f.pinv r))
  obtain ⟨hk0,hk25,hkr⟩ := familyH_spec _ (noncollinear_fixed5 _ hnc2)
  refine ⟨transport5 k (transport5 g (transport5 f a)),
    minimal_transport5 k 5 _ (minimal_transport5 g 5 _ (minimal_transport5 f 5 a hm)),
    (timeIs_transport5 k 5 _ 2).mpr ((timeIs_transport5 g 5 _ 2).mpr
      ((timeIs_transport5 f 5 _ 2).mpr ht)), ?_, ?_, ?_⟩
  · change a (f.p (g.p (k.p 0))) = true
    rw [hk0,hg0,hf]; exact hp
  · change a (f.p (g.p (k.p 25))) = true
    rw [hk25,hgq,f.pp]; exact hq
  · change a (f.p (g.p (k.p 30))) = true
    rw [hkr,g.pp,f.pp]; exact hr
end Percolation
namespace Percolation
set_option autoImplicit false

theorem witness_satisfies_normalizedCNF5 (a : Infection 5)
    (hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    ∃ val : SatVar → Bool, ∀ c ∈ normalizedCNF5, CNF.Holds val c := by
  obtain ⟨b, hbm, hbt, h0, h25, h30⟩ := normalize_witness5 a hm ht
  let x := step PG5 5 b
  let val := assignment5 b x (active5 b) (active5 x)
      (fun v => rounds PG5 5 (erase b v) 31)
  refine ⟨val, ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact witness_satisfies_inputCNF5 b hbm hbt c hc
  · simp only [normalizedUnits5, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨(.a 0,false),by simp,by simpa [val,assignment5] using h0⟩
    · exact ⟨(.a 25,false),by simp,by simpa [val,assignment5] using h25⟩
    · exact ⟨(.a 30,false),by simp,by simpa [val,assignment5] using h30⟩

def GeneratedNormalizedUnsat5 : Prop :=
  ¬ ∃ val : SatVar → Bool, ∀ c ∈ normalizedCNF5, CNF.Holds val c

theorem normalized_unsat_implies_noMinimal5 (h : GeneratedNormalizedUnsat5) :
    NoMinimalTwoRound5 := by
  rintro ⟨a,hm,ht⟩
  exact h (witness_satisfies_normalizedCNF5 a hm ht)

theorem not_conjecture20_normalized (h : GeneratedNormalizedUnsat5) : ¬ Conjecture20 :=
  not_conjecture20 (normalized_unsat_implies_noMinimal5 h)
#print axioms witness_satisfies_normalizedCNF5
#print axioms not_conjecture20_normalized
end Percolation
