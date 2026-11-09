import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace XorMagic
abbrev Bits (n : ℕ) := Fin n → ZMod 2

variable {V : Type} [Fintype V] [DecidableEq V]

def OpenMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, ∑ u ∈ G.neighborFinset v, l u = 0

def ClosedMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, l v + ∑ u ∈ G.neighborFinset v, l u = 0

omit [DecidableEq V] in
theorem card_of_label {n : ℕ} (l : V ≃ Bits n) : Fintype.card V = 2^n := by
  simpa [Bits, Fintype.card_fun] using Fintype.card_congr l

def OpenExists (n d : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ OpenMagic G n

def ClosedExists (n d : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ ClosedMagic G n

def PrintedAt (n : ℕ) : Prop :=
  (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧
  (∀ d, Even d → 4 ≤ d → d ≤ 2^n-4 → ClosedExists n d)

def CorrectedAt (n : ℕ) : Prop :=
  (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧
  (∀ d, Even d → 4 ≤ d → d ≤ 2^n-6 → ClosedExists n d)

theorem bits_add_self {n : ℕ} (x : Bits n) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem cubic_obstruction {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (reg : G.IsRegularOfDegree 3) (l : V ≃ Bits n)
    (magic : ∀ v, ∑ u ∈ G.neighborFinset v, l u = 0) : False := by
  let z := l.symm 0
  have hz : l z = 0 := l.apply_symm_apply 0
  have hc : (G.neighborFinset z).card = 3 := by simpa using reg z
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset z).card)
  have hzu : z ∈ G.neighborFinset u := by
    simpa only [SimpleGraph.mem_neighborFinset] using (show G.Adj z u from (by simpa using hu)).symm
  have he : ((G.neighborFinset u).erase z).card = 2 := by
    rw [Finset.card_erase_of_mem hzu]
    have : (G.neighborFinset u).card = 3 := by simpa using reg u
    omega
  obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp he
  have hs : ∑ x ∈ (G.neighborFinset u).erase z, l x = 0 := by
    have h := magic u
    rw [← Finset.sum_erase_add _ _ hzu, hz, add_zero] at h
    exact h
  rw [heq] at hs
  have hs' : l a + l b = 0 := by simpa [hab] using hs
  have hequal : l a = l b := by
    have h := congrArg (fun x => x + l b) hs'
    simpa [add_assoc, bits_add_self] using h
  exact hab (l.injective hequal)

-- Complement identity proved from a disjoint partition of all vertices.
theorem complement_identity {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : V → Bits n) (total : ∑ v, l v = 0) (v : V) :
    (∑ u ∈ Gᶜ.neighborFinset v, l u) = l v + ∑ u ∈ G.neighborFinset v, l u := by
  classical
  have hn : v ∉ G.neighborFinset v := by simp
  have hd : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro u hu hc
    have ha : G.Adj v u := by simpa using hu
    have hb : Gᶜ.Adj v u := by simpa using hc
    exact hb.2 ha
  have hp : insert v (G.neighborFinset v ∪ Gᶜ.neighborFinset v) = Finset.univ := by
    ext u
    simp only [Finset.mem_insert, Finset.mem_union, SimpleGraph.mem_neighborFinset,
      SimpleGraph.compl_adj, Finset.mem_univ, iff_true]
    by_cases h : u = v
    · exact Or.inl h
    · by_cases ha : G.Adj v u
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨Ne.symm h, ha⟩)
  have hv : v ∉ G.neighborFinset v ∪ Gᶜ.neighborFinset v := by simp
  have hs := total
  rw [← hp, Finset.sum_insert hv, Finset.sum_union hd] at hs
  have hs' : (l v + ∑ u ∈ G.neighborFinset v, l u) +
      (∑ u ∈ Gᶜ.neighborFinset v, l u) = 0 := by simpa [add_assoc] using hs
  apply add_left_cancel (a := l v + ∑ u ∈ G.neighborFinset v, l u)
  rw [hs', bits_add_self]


 theorem total_bits_four : (∑ x : Bits 4, x) = 0 := by decide

theorem no_closed_twelve (G : SimpleGraph V) [DecidableRel G.Adj]
    (reg : G.IsRegularOfDegree 12) (h : ClosedMagic G 4) : False := by
  classical
  obtain ⟨_, l, hl⟩ := h
  have hc := card_of_label l
  have hr : Gᶜ.IsRegularOfDegree 3 := by
    have hh := reg.compl
    simpa [hc] using hh
  have ht : ∑ v, l v = 0 := by
    rw [Equiv.sum_comp l (fun x : Bits 4 => x)]
    exact total_bits_four
  apply cubic_obstruction Gᶜ hr l
  intro v
  rw [complement_identity G l ht v]
  exact hl v

theorem not_closed_exists_four_twelve : ¬ ClosedExists 4 12 := by
  rintro ⟨V, f, e, G, dec, reg, h⟩
  exact no_closed_twelve G reg h

theorem not_printed_at_four : ¬ PrintedAt 4 := by
  intro h
  exact not_closed_exists_four_twelve (h.2 12 (by decide) (by decide) (by decide))

theorem not_printed_all : ¬ (∀ n, PrintedAt n) := by
  intro h
  exact not_printed_at_four (h 4)

theorem not_printed_ge_four : ¬ (∀ n, 4 ≤ n → PrintedAt n) := by
  intro h
  exact not_printed_at_four (h 4 le_rfl)
theorem not_printed_positive : ¬ (∀ n, 0 < n → PrintedAt n) := by
  intro h
  exact not_printed_at_four (h 4 (by decide))
end XorMagic
