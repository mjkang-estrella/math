import SourceSemantics
namespace ChanLevine
variable {n : ℕ}

/-- A finite labelled legal execution, retaining the actual fired vertices. -/
inductive LegalWord : SignedConfig n → List (ZMod n) → SignedConfig n → Prop
  | nil (c) : LegalWord c [] c
  | cons {c d w} (v) : 0 < c.x v → LegalWord (fire c v) w d → LegalWord c (v :: w) d

theorem LegalWord.reach {c d : SignedConfig n} {w} (h : LegalWord c w d) : Reach c d := by
  induction h with
  | nil => exact .refl
  | cons v hv _ ih => exact (Relation.ReflTransGen.single ⟨v, hv, rfl⟩).trans ih

theorem reach_has_word {c d : SignedConfig n} (h : Reach c d) :
    ∃ w, LegalWord c w d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .nil _⟩
  | head h _ ih =>
    obtain ⟨v, hv, rfl⟩ := h
    obtain ⟨w, hw⟩ := ih
    exact ⟨v :: w, .cons v hv hw⟩

/-- Definition 5.2 alone supplies a nonempty closed execution. -/
theorem recurrent_closed_word {c : SignedConfig n} (hc : Recurrent c) :
    ∃ w, w ≠ [] ∧ LegalWord c w c := by
  obtain ⟨d, v, hv, rfl⟩ := hc.1
  have hr : Related c (fire c v) :=
    ⟨fire c v, Relation.ReflTransGen.single ⟨v, hv, rfl⟩, .refl⟩
  obtain ⟨w, hw⟩ := reach_has_word (hc.2 _ hr)
  exact ⟨v :: w, List.cons_ne_nil _ _, .cons v hv hw⟩

theorem nonnegative_fire_at {c : SignedConfig n} {v k : ZMod n}
    (hv : 0 < c.x v) (hk : 0 ≤ c.x k) : 0 ≤ (fire c v).x k := by
  by_cases he : k = v
  · subst k
    dsimp [fire]
    simp only [ite_true]
    split_ifs <;> omega
  · dsimp [fire]
    simp only [he, ite_false, sub_zero]
    split_ifs <;> omega

theorem LegalWord.nonnegative {c d : SignedConfig n} {w} (h : LegalWord c w d)
    {k : ZMod n} (hk : 0 ≤ c.x k) : 0 ≤ d.x k := by
  induction h with
  | nil => exact hk
  | cons v hv _ ih => exact ih (nonnegative_fire_at hv hk)

/-- Once a vertex fires legally, its chip count stays nonnegative forever. -/
theorem LegalWord.nonnegative_of_mem {c d : SignedConfig n} {w}
    (h : LegalWord c w d) {k : ZMod n} (hk : k ∈ w) : 0 ≤ d.x k := by
  induction h with
  | nil => simp at hk
  | cons v hv hw ih =>
    rcases List.mem_cons.mp hk with he | he
    · subst k
      apply hw.nonnegative
      apply nonnegative_fire_at hv
      omega
    · exact ih he

/-- The graph-specific coverage step for a closed trajectory remains open. -/
def ClosedCoverage : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (c : SignedConfig n) (w : List (ZMod n)),
    w ≠ [] → LegalWord c w c → ∀ k, k ∈ w

theorem recurrent_nonnegative_of_coverage (h : ClosedCoverage) (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) (c : SignedConfig n) (hc : Recurrent c) : ∀ k, 0 ≤ c.x k := by
  obtain ⟨w, hw, hl⟩ := recurrent_closed_word hc
  intro k
  exact hl.nonnegative_of_mem (h n hn c w hw hl k)
end ChanLevine
