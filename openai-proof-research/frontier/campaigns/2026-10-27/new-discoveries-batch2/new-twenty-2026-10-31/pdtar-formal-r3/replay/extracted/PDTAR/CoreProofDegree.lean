import PDTAR.CoreProofHub
namespace PDTAR
set_option linter.unusedVariables false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 5(ii), obtained by applying step (i) to the swapped partition. -/
theorem core_hub_step_ii {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) {a c : V}
    (haA : a ∈ A) (hcB : c ∈ B)
    (hcross : ∀ b ∈ B, H.Adj a b ↔ b = c) :
    (∀ b ∈ B, b ≠ c → H.Adj c b) ∧
    (∀ x ∈ B, H.Adj a x ↔ x = c) ∧
    (∀ b ∈ B, b ≠ c → ∀ d ∈ B, H.Adj b d ↔ d = c) := by
  have hi := core_hub_step_i hk he ha hb haA hcB hcross
  exact core_hub_step_i (completeBetween_swap hk) he hb ha hcB haA hi.2.1

/-- The pair forts away from the hub all coincide. -/
theorem core_hub_pair_eq {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) {a c x y : V} (haA : a ∈ A)
    (hcB : c ∈ B) (hax : a ≠ x) (hay : a ≠ y)
    (hac : H.Adj a c) (hA : ∀ z ∈ A, z ≠ a → H.Adj a z)
    (hB : ∀ b ∈ B, b ≠ c → ∀ d ∈ B, H.Adj b d ↔ d = c)
    {F : Finset V} (hC : closed H F = B ∪ {x,y}) : F = B.erase c := by
  classical
  have haC : a ∉ closed H F := by
    rw [hC]
    simp only [mem_union,mem_insert,mem_singleton,not_or]
    exact ⟨fun h => hk.1.not_both haA h,hax,hay⟩
  have hsub : F ⊆ B.erase c := by
    intro u hu
    have hua : u ≠ a := fun heq => haC (heq ▸ subset_closed H F hu)
    have huB : u ∈ B := by
      rcases hk.1.mem_or u with huA | huB
      · exact False.elim (haC (core_fort_neighbor hu (hA u huA hua).symm))
      · exact huB
    have huc : u ≠ c := by
      intro heq
      exact haC (core_fort_neighbor (heq ▸ hu) hac.symm)
    exact mem_erase.mpr ⟨huc,huB⟩
  apply subset_antisymm hsub
  intro b hb
  obtain ⟨hbc,hbB⟩ := mem_erase.mp hb
  have hbC : b ∈ closed H F := by rw [hC]; exact mem_union.mpr (.inl hbB)
  rcases (mem_closed H F b).mp hbC with hbF | ⟨u,hu,hub⟩
  · exact hbF
  · have huB := mem_of_mem_erase (hsub hu)
    have huc := (hB b hbB hbc u huB).mp hub.symm
    exact False.elim ((mem_erase.mp (hsub hu)).1 huc)

/-- Lemma 5(iii), one side of the counting argument. -/
theorem core_hub_count_side {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) {a c : V}
    (haA : a ∈ A) (hcB : c ∈ B) (hac : H.Adj a c)
    (hA : ∀ z ∈ A, z ≠ a → H.Adj a z)
    (hB : ∀ b ∈ B, b ≠ c → ∀ d ∈ B, H.Adj b d ↔ d = c) : A.card = 3 := by
  classical
  obtain ⟨x,hx,hxa,_⟩ := core_third ha a a
  obtain ⟨y,hy,hya,hyx⟩ := core_third ha a x
  obtain ⟨F,_,hC⟩ := pair_fort hk he ha (by omega) hx hy hyx.symm
  have hF := core_hub_pair_eq hk haA hcB hxa.symm hya.symm hac hA hB hC
  have hsub : A ⊆ {a,x,y} := by
    intro z hz
    by_cases hza : z = a
    · simp [hza]
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzy : z = y
    · simp [hzy]
    obtain ⟨F',_,hC'⟩ := pair_fort hk he ha (by omega) hx hz (Ne.symm hzx)
    have hF' := core_hub_pair_eq hk haA hcB hxa.symm (Ne.symm hza) hac hA hB hC'
    have hyC : y ∈ closed H F' := by rw [hF',← hF,hC]; simp
    rw [hC'] at hyC
    rcases mem_union.mp hyC with hyB | hyp
    · exact False.elim (hk.1.not_both hy hyB)
    · simp only [mem_insert,mem_singleton] at hyp
      exact False.elim (hyp.elim hyx (Ne.symm hzy))
  have hc := card_le_card hsub
  have ht : ({a,x,y} : Finset V).card ≤ 3 := by
    calc
      _ ≤ 1 + ({x,y} : Finset V).card := by simpa [Nat.add_comm] using card_insert_le a ({x,y} : Finset V)
      _ ≤ 3 := by have := card_insert_le x ({y} : Finset V); simp only [card_singleton] at this; omega
  omega

/-- Lemma 5: the single-cross-neighbour case forces precisely the exceptional sizes. -/
theorem core_cross_singleton_sizes {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) {a c : V}
    (haA : a ∈ A) (hcB : c ∈ B)
    (hcross : ∀ b ∈ B, H.Adj a b ↔ b = c) : A.card = 3 ∧ B.card = 3 := by
  have hi := core_hub_step_i hk he ha hb haA hcB hcross
  have hii := core_hub_step_ii hk he ha hb haA hcB hcross
  have hac := (hcross c hcB).mpr rfl
  exact ⟨core_hub_count_side hk he ha hb haA hcB hac hi.1 hii.2.2,
    core_hub_count_side (completeBetween_swap hk) he hb ha hcB haA hac.symm hii.1 hi.2.2⟩

/-- Corollary 5': away from (3,3), each cross neighbour has a different cross neighbour. -/
theorem core_cross_two {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) (hn : A.card ≠ 3 ∨ B.card ≠ 3)
    {a : V} (haA : a ∈ A) :
    ∃ b ∈ B, ∃ c ∈ B, b ≠ c ∧ H.Adj a b ∧ H.Adj a c := by
  classical
  obtain ⟨b,hbB,hab⟩ := core_cross_nonempty hk he ha (by omega) haA
  by_contra! h
  have hone : ∀ c ∈ B, H.Adj a c ↔ c = b := by
    intro c hc
    constructor
    · intro hac
      by_contra hcb
      exact h b hbB c hc (Ne.symm hcb) hab hac
    · rintro rfl; exact hab
  have hs := core_cross_singleton_sizes hk he ha hb haA hbB hone
  exact hn.elim (fun h => h hs.1) (fun h => h hs.2)
end PDTAR
