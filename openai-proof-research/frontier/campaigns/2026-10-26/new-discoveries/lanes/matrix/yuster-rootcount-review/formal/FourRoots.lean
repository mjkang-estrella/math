import Mathlib

open Set Polynomial Finset

namespace FourRoots

lemma root_between_neg_pos (p : ℝ[X]) {a b : ℝ} (hab : a<b)
    (ha : p.eval a<0) (hb : 0<p.eval b) :
    ∃ x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,hx,hpx⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn
    (show (0:ℝ)∈Ioo (p.eval a) (p.eval b) from ⟨ha,hb⟩)
  exact ⟨x,hx.1,hx.2,hpx⟩

lemma root_between_pos_neg (p : ℝ[X]) {a b : ℝ} (hab : a<b)
    (ha : 0<p.eval a) (hb : p.eval b<0) :
    ∃ x, a<x ∧ x<b ∧ p.eval x=0 := by
  obtain ⟨x,hx,hpx⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn
    (show (0:ℝ)∈Ioo (p.eval b) (p.eval a) from ⟨hb,ha⟩)
  exact ⟨x,hx.1,hx.2,hpx⟩

/-- Five alternating strict signs give four ordered interior roots. -/
theorem ordered_four_roots (p : ℝ[X])
    (h0 : p.eval (1/100)<0) (h1 : 0<p.eval (1/10))
    (h2 : p.eval (1/2)<0) (h3 : 0<p.eval (3/5)) (h4 : p.eval (4/5)<0) :
    ∃ a b c d : ℝ, 0<a ∧ a<b ∧ b<c ∧ c<d ∧ d<1 ∧
      p.eval a=0 ∧ p.eval b=0 ∧ p.eval c=0 ∧ p.eval d=0 := by
  obtain ⟨a,ha0,ha1,hpa⟩ := root_between_neg_pos p (by norm_num : (1/100:ℝ)<1/10) h0 h1
  obtain ⟨b,hb0,hb1,hpb⟩ := root_between_pos_neg p (by norm_num : (1/10:ℝ)<1/2) h1 h2
  obtain ⟨c,hc0,hc1,hpc⟩ := root_between_neg_pos p (by norm_num : (1/2:ℝ)<3/5) h2 h3
  obtain ⟨d,hd0,hd1,hpd⟩ := root_between_pos_neg p (by norm_num : (3/5:ℝ)<4/5) h3 h4
  exact ⟨a,b,c,d,by linarith,by linarith,by linarith,by linarith,by linarith,
    hpa,hpb,hpc,hpd⟩

noncomputable def interiorRootCount (p : ℝ[X]) : ℕ :=
  (p.roots.filter (fun x => 0<x ∧ x<1)).card

/-- The source convention counts multiplicity; four distinct roots suffice. -/
theorem four_le_interiorRootCount (p : ℝ[X])
    (h0 : p.eval (1/100)<0) (h1 : 0<p.eval (1/10))
    (h2 : p.eval (1/2)<0) (h3 : 0<p.eval (3/5)) (h4 : p.eval (4/5)<0) :
    4 ≤ interiorRootCount p := by
  classical
  have hp : p≠0 := by intro hz; simp [hz] at h0
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,hd,hpa,hpb,hpc,hpd⟩ :=
    ordered_four_roots p h0 h1 h2 h3 h4
  have hmem (x : ℝ) (hx : 0<x ∧ x<1) (hpx : p.eval x=0) :
      x∈(p.roots.filter (fun y => 0<y ∧ y<1)).toFinset := by
    simp [Polynomial.mem_roots hp, Polynomial.IsRoot, hpx, hx]
  have hcard : ({a,b,c,d}:Finset ℝ).card=4 := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd,
      ne_of_lt (lt_trans hab hbc), ne_of_lt (lt_trans hbc hcd),
      ne_of_lt (lt_trans hab (lt_trans hbc hcd))]
  have hsub : ({a,b,c,d}:Finset ℝ) ⊆
      (p.roots.filter (fun y => 0<y ∧ y<1)).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx|hx|hx|hx
    · subst x; exact hmem a ⟨ha,by linarith⟩ hpa
    · subst x; exact hmem b ⟨by linarith,by linarith⟩ hpb
    · subst x; exact hmem c ⟨by linarith,by linarith⟩ hpc
    · subst x; exact hmem d ⟨by linarith,hd⟩ hpd
  calc
    4 = ({a,b,c,d}:Finset ℝ).card := hcard.symm
    _ ≤ (p.roots.filter (fun y => 0<y ∧ y<1)).toFinset.card := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _

end FourRoots
