import Spectral
import Semantics
set_option autoImplicit false
namespace SpectralExclusion
open SpectralSemantics

theorem raw_formula (a b c d : ℕ) :
    value (raw a b c d) = radius a b c d := by
  rw [radius_formula (by positivity) (by positivity) (by positivity) (by positivity)]
  have h : ((Int.natAbs ((a:ℤ)-d):ℝ))^2 = ((a:ℝ)-d)^2 := by
    have hh : ((Int.natAbs ((a:ℤ)-d):ℤ))^2 = ((a:ℤ)-d)^2 := by
      rw [Int.natCast_natAbs, sq_abs]
    have hh' := congrArg (fun x : ℤ => (x:ℝ)) hh
    simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_sub] using hh'
  simp only [value, raw, plusRoot, Nat.cast_add, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_ofNat]
  rw [h]

noncomputable def sourceOmega (A : Finset ℝ) : Finset ℝ := by
  classical
  exact (A ×ˢ A ×ˢ A ×ˢ A).image (fun t => radius t.1 t.2.1 t.2.2.1 t.2.2.2)

noncomputable def castSet (A : Finset ℕ) : Finset ℝ := A.image Nat.cast

theorem omega_source (A : Finset ℕ) : sourceOmega (castSet A) = omega A := by
  classical
  ext r
  simp only [sourceOmega, castSet, omega, tuples, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a,b,c,d⟩, ⟨⟨aa,haa,rfl⟩,⟨bb,hbb,rfl⟩,⟨cc,hcc,rfl⟩,dd,hdd,rfl⟩,hr⟩
    exact ⟨(aa,bb,cc,dd), ⟨haa,hbb,hcc,hdd⟩, (raw_formula aa bb cc dd).trans hr⟩
  · rintro ⟨⟨a,b,c,d⟩, ⟨ha,hb,hc,hd⟩,hr⟩
    refine ⟨(a,b,c,d), ⟨⟨a,ha,rfl⟩, ⟨b,hb,rfl⟩,⟨c,hc,rfl⟩,d,hd,rfl⟩, ?_⟩
    exact (raw_formula a b c d).symm.trans hr

noncomputable def rMin (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ A : Finset ℝ, A.card=k ∧ (∀ a ∈ A, 0<a) ∧ (sourceOmega A).card=n}

def SourceConjecture : Prop := ∀ (k : ℕ) (B : Finset ℝ),
  1 ≤ k → B.card=k-1 → (∀ b ∈ B, 0<b) →
    (sourceOmega (insert 0 B)).card < rMin k

theorem rMin_five_le : rMin 5 ≤ 115 := by
  have h : (sourceOmega (castSet positiveSet)).card ≤ 115 := by
    rw [omega_source]
    exact positive_count_le
  apply le_trans _ h
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨castSet positiveSet, ?_, ?_, rfl⟩
  · norm_num [castSet, positiveSet]
  · intro a ha
    simp only [castSet, positiveSet, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with ⟨n, hn, rfl⟩
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem source_conjecture_refuted : ¬SourceConjecture := by
  intro h
  let B : Finset ℝ := castSet {2,3,5,7}
  have hb : B.card = 5-1 := by norm_num [B, castSet]
  have hp : ∀ b ∈ B, 0 < b := by
    intro b hb
    simp only [B, castSet, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with ⟨n, hn, rfl⟩
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  have hz : insert 0 B = castSet zeroSet := by simp [B, castSet, zeroSet]
  have hc := h 5 B (by norm_num) hb hp
  rw [hz, omega_source, zero_count] at hc
  have hm := rMin_five_le
  omega

#print axioms source_conjecture_refuted
#print axioms raw_formula
#print axioms omega_source
end SpectralExclusion
