import Final
namespace Rainbow
open SimpleGraph
theorem rainbow_insert_iff {V C : Type*} {c : V → C} {S : V → Prop} {x : V} (hx : ¬ S x) :
    RainbowOn c (fun v => S v ∨ v = x) ↔
      RainbowOn c S ∧ ∀ v, S v → c v ≠ c x := by
  constructor
  · intro h
    refine ⟨fun u v hu hv hc => h u v (Or.inl hu) (Or.inl hv) hc, ?_⟩
    intro v hv hc
    have he := h v x (Or.inl hv) (Or.inr rfl) hc
    exact hx (he ▸ hv)
  · rintro ⟨h, hc⟩ u v hu hv he
    rcases hu with hu | rfl <;> rcases hv with hv | rfl
    · exact h u v hu hv he
    · exact (hc u hu he).elim
    · exact (hc v hv he.symm).elim
    · rfl

def SourceValid {V : Type*} (H : SimpleGraph V) {k : Nat} (c : V → Fin k) : Prop :=
  ∀ x y, x ≠ y → ∃ S : V → Prop, ¬ S x ∧ ¬ S y ∧ RainbowOn c S ∧
    (H.Adj x y → RainbowOn c (fun v => S v ∨ v = x) ∨ RainbowOn c (fun v => S v ∨ v = y)) ∧
    ¬ (cutGraph H S x y).Reachable x y

theorem valid_iff_sourceValid {V : Type*} {H : SimpleGraph V} {k : Nat} {c : V → Fin k} :
    Valid H c ↔ SourceValid H c := by
  constructor
  · intro h x y hxy
    obtain ⟨S,hx,hy,hr,he,hs⟩ := h x y hxy
    refine ⟨S,hx,hy,hr,?_,hs⟩
    intro hAdj
    rcases he hAdj with hh | hh
    · exact Or.inl ((rainbow_insert_iff hx).mpr ⟨hr,hh⟩)
    · exact Or.inr ((rainbow_insert_iff hy).mpr ⟨hr,hh⟩)
  · intro h x y hxy
    obtain ⟨S,hx,hy,hr,he,hs⟩ := h x y hxy
    refine ⟨S,hx,hy,hr,?_,hs⟩
    intro hAdj
    rcases he hAdj with hh | hh
    · exact Or.inl ((rainbow_insert_iff hx).mp hh).2
    · exact Or.inr ((rainbow_insert_iff hy).mp hh).2

noncomputable def sourceRvd {V : Type*} (H : SimpleGraph V) : Nat :=
  sInf {k : Nat | ∃ c : V → Fin k, SourceValid H c}

theorem sourceRvd_eq {V : Type*} (H : SimpleGraph V) : sourceRvd H = rvd H := by
  unfold sourceRvd rvd
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, valid_iff_sourceValid]

theorem rvd_isLeast {V : Type*} {H : SimpleGraph V}
    (hn : ∃ k, ∃ c : V → Fin k, Valid H c) :
    IsLeast {k : Nat | ∃ c : V → Fin k, Valid H c} (rvd H) := by
  exact ⟨csInf_mem hn, fun k hk => csInf_le (OrderBot.bddBelow _) hk⟩

theorem mathdb_346167_literal :
    ¬ (∀ (n : Nat) (H : SimpleGraph (Fin n)), 8 ≤ n →
      H.Connected → Hᶜ.Connected → n ≤ sourceRvd H + sourceRvd Hᶜ) := by
  simpa only [sourceRvd_eq] using mathdb_346167
end Rainbow
#print axioms Rainbow.mathdb_346167_literal
