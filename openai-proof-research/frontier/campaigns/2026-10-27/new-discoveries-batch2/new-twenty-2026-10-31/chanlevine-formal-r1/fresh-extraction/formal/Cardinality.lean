import SourceSemantics
open scoped BigOperators
namespace ChanLevine
variable {n : ℕ} [NeZero n]

theorem chip_bound {c : Config n} {m : ℕ} (h : chipLevel c = m) (k : ZMod n) :
    c.x k < m+1 := by
  have hh : c.x k ≤ ∑ j : ZMod n, c.x j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (c.x j)) (Finset.mem_univ k)
  change c.x k ≤ chipLevel c at hh
  omega

noncomputable def encodeLevel (m : ℕ) (c : {c : Config n // chipLevel c = m}) :
    (ZMod n → Fin (m+1)) × (ZMod n → Bool) :=
  (fun k => ⟨c.val.x k, chip_bound c.property k⟩, c.val.q)

theorem encodeLevel_injective (m : ℕ) : Function.Injective (encodeLevel (n := n) m) := by
  intro a b h
  have hx : a.val.x = b.val.x := by
    funext k
    exact congrArg Fin.val (congrFun (congrArg Prod.fst h) k)
  have hq : a.val.q = b.val.q := congrArg Prod.snd h
  have he : ∀ c d : Config n, c.x = d.x → c.q = d.q → c = d := by
    rintro ⟨x,q⟩ ⟨y,r⟩ hx hq
    cases hx; cases hq; rfl
  exact Subtype.ext (he _ _ hx hq)

instance level_finite (m : ℕ) : Finite {c : Config n // chipLevel c = m} :=
  Finite.of_injective _ (encodeLevel_injective m)

instance test_finite (m : ℕ) (i : ZMod n) :
    Finite {c : Config n // CycleTest c ∧ chipLevel c = m ∧ chipWeight c = i} :=
  Finite.of_injective (fun c => (⟨c.val, c.property.2.1⟩ : {d : Config n // chipLevel d = m}))
    (by intro a b h; exact Subtype.ext (congrArg (fun t : {c : Config n // chipLevel c = m} => t.val) h))

instance component_finite (m : ℕ) (i : ZMod n) :
    Finite {d : Config n // NatRecurrent d ∧ d.lift ∈ C m i} := by
  have hh : ∀ d : {d : Config n // NatRecurrent d ∧ d.lift ∈ C m i}, chipLevel d.val = m := by
    intro d
    have h := level_related d.property.2
    change level (canonical m i).lift = level d.val.lift at h
    rw [level_lift, level_lift, canonical_level] at h
    exact_mod_cast h.symm
  exact Finite.of_injective (fun d => (⟨d.val, hh d⟩ : {c : Config n // chipLevel c = m}))
    (by intro a b h; exact Subtype.ext (congrArg (fun t : {c : Config n // chipLevel c = m} => t.val) h))

omit [NeZero n] in
theorem component_eq_of_mutual {a b : SignedConfig n} (h : Reach a b ∧ Reach b a) :
    component a = component b := by
  ext c
  constructor
  · rintro ⟨d, had, hcd⟩
    exact ⟨d, h.2.trans had, hcd⟩
  · rintro ⟨d, hbd, hcd⟩
    exact ⟨d, h.1.trans hbd, hcd⟩

/-- Literal uniqueness of the legal-relation component, still conditional. -/
theorem existsUnique_component_conditional (hc : CycleTestBridge) (ha : CanonicalTest)
    (hu : ConnectedFibres) (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m)
    (i : ZMod n) :
    ∃! S : Set (SignedConfig n), ∃ a : Config n,
      NatRecurrent a ∧ chipLevel a = m ∧ chipWeight a = i ∧ S = component a.lift := by
  have hh := unique_component_conditional hc ha hu n m hn hm i
  refine ⟨C m i, ⟨canonical m i, hh.1, hh.2.1, hh.2.2.1, rfl⟩, ?_⟩
  rintro S ⟨a, har, hal, haw, rfl⟩
  have hr : Related (canonical m i).lift a.lift :=
    (hh.2.2.2 a har).mpr ⟨hal, haw⟩
  exact (component_eq_of_mutual ((recurrent_related_iff hh.1 har).mp hr)).symm
end ChanLevine
