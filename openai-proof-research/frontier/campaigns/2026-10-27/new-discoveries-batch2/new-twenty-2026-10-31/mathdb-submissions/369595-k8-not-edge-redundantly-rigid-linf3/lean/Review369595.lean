import K8Main

/-!
# The reviewer's endpoint

The definitions in the namespace `Review369595` are copied verbatim from
REVIEW-369595.md, §6 (the coordinate-specialised form of the source
definitions: flexes are vectors whose `i`-th coordinates agree across each edge
of colour `i`, trivial flexes are translations).  Both `K8Endpoint` and
`RefutationEndpoint` are proved, through the same combinatorial core
`CDK.k8_no_good`.
-/

namespace Review369595

abbrev Placement (n d : ℕ) := Fin n → Fin d → ℝ
abbrev EdgeRel (n : ℕ) := Fin n → Fin n → Prop

def complete (n : ℕ) : EdgeRel n := fun v w => v ≠ w

def removeEdge {n : ℕ} (E : EdgeRel n) (v w : Fin n) : EdgeRel n :=
  fun a b => E a b ∧ ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v))

def Dominates {n d : ℕ} (p : Placement n d) (v w : Fin n) (i : Fin d) : Prop :=
  0 < |p v i - p w i| ∧
    ∀ j : Fin d, j ≠ i → |p v j - p w j| < |p v i - p w i|

def WellPositioned {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  ∀ v w : Fin n, E v w → ∃ i : Fin d, Dominates p v w i

def Flex {n d : ℕ} (E : EdgeRel n) (p u : Placement n d) : Prop :=
  ∀ (v w : Fin n) (i : Fin d), E v w → Dominates p v w i → u v i = u w i

def InfRigid {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  WellPositioned E p ∧
    ∀ u : Placement n d, Flex E p u → ∃ t : Fin d → ℝ, ∀ v, u v = t

def Redundant {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  InfRigid E p ∧ ∀ v w : Fin n, E v w → InfRigid (removeEdge E v w) p

def ERConjecture : Prop :=
  ∀ d n : ℕ, 2 ≤ d → 2 * d + 2 ≤ n →
    ∃ p : Placement n d, Redundant (complete n) p

def K8Endpoint : Prop := ¬ ∃ p : Placement 8 3, Redundant (complete 8) p
def RefutationEndpoint : Prop := ¬ ERConjecture

open K8 in
theorem good_of_redundant {p : Placement 8 3} (h : Redundant (complete 8) p) : Good p := by
  obtain ⟨⟨hwp, -⟩, hdel⟩ := h
  constructor
  · intro u v huv
    obtain ⟨i, -, hi⟩ := hwp v u (Ne.symm huv)
    exact ⟨i, fun j hj => by simpa using hi j hj⟩
  · intro u v huv S k ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    by_contra hno
    push Not at hno
    obtain ⟨-, hflex⟩ := hdel u v huv
    let U : Placement 8 3 := fun x i => if i = k ∧ x ∈ S then 1 else 0
    have hU : Flex (removeEdge (complete 8) u v) p U := by
      intro a b i hab hdom
      by_cases hik : i = k
      · subst hik
        have hd : Dom (p a - p b) i := fun j hj => by simpa using hdom.2 j hj
        by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
        · simp [U, ha, hb]
        · exfalso
          refine hno a ha b hb ?_ ?_ hd.sub_comm
          · intro h1 h2; exact hab.2 (Or.inl ⟨h1, h2⟩)
          · intro h1 h2; exact hab.2 (Or.inr ⟨h1, h2⟩)
        · exfalso
          refine hno b hb a ha ?_ ?_ hd
          · intro h1 h2; exact hab.2 (Or.inr ⟨h2, h1⟩)
          · intro h1 h2; exact hab.2 (Or.inl ⟨h2, h1⟩)
        · simp [U, ha, hb]
      · simp [U, hik]
    obtain ⟨t, ht⟩ := hflex U hU
    have := congr_fun ((ht a₀).trans (ht b₀).symm) k
    simp [U, ha₀, hb₀] at this

theorem k8_counterexample : K8Endpoint := by
  rintro ⟨p, hp⟩
  exact CDK.k8_no_good ⟨p, good_of_redundant hp⟩

theorem cdk_source_refuted : RefutationEndpoint := fun candidate =>
  k8_counterexample (candidate 3 8 (by decide) (by decide))

end Review369595
