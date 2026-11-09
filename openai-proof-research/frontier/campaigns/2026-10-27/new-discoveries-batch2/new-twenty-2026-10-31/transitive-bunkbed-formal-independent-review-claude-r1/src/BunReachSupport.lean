/-
# Bunkbed E7 (r20): the literal Reach/state membership bridge

Main theorem `Bun.stf_reach_strong`: for `j < n`, a full outcome `ω`, a vertex
`i : Fin n` and a layer `σ`, membership of `i.val` in the layer-`σ` component of
the prefix state `stf n u.val j (wres n j ω)` is equivalent to
`u.val ≤ i.val ∧ i.val ≤ j ∧ Reach n ω (u,false) (i,σ)`.

The proof is the joint prefix induction prescribed by the review: state→Reach
uses the closed indicator forms `X ∨ (Z ∧ Y)` / `Y ∨ (Z ∧ X)`; Reach→state uses
an inner `ReflTransGen` derivation induction for endpoints at the new index
`j+1`, where a final vertical arc consumes the shorter derivation's
opposite-layer membership through the coupled `ind` equations.  No cyclic
rewriting of `reach_char` is used.
-/
import BunkbedBase
import BunState
import BunBridge
import BunReach
import BunOldStable
import BunNewIndicators
import BunHorWitness
import BunUpperSupport
import BunLowerSupport

namespace Bun

/-! ### Token transport -/

/-- Horizontal tokens are equal when the underlying index values agree. -/
theorem htok_congr {n : Nat} {i i' j j' : Fin n}
    (hi : (i : Nat) = (i' : Nat)) (hj : (j : Nat) = (j' : Nat))
    (h : (i : Nat) < (j : Nat)) (h' : (i' : Nat) < (j' : Nat)) (l : Bool) :
    htok i j h l = htok i' j' h' l := by
  have hii : i = i' := Fin.ext hi
  have hjj : j = j' := Fin.ext hj
  subst hii
  subst hjj
  rfl

/-- Window value of a fresh horizontal token, in outcome form. -/
theorem wres_fresH {n m : Nat} (hm : m < n) (ω : Out n) (i : Nat) (hic : i < m) (l : Bool) :
    wres n m ω (fresH hm i hic l) =
      ω (htok ⟨i, Nat.lt_trans hic hm⟩ ⟨m, hm⟩ hic l) := by
  unfold wres fresH
  congr 1

/-- Window value of the fresh vertical token, in outcome form. -/
theorem wres_fresV {n m : Nat} (hm : m < n) (ω : Out n) :
    wres n m ω (fresV (n := n) (m := m) hm) = ω (vtok ⟨m, hm⟩) := rfl

theorem fresV_congr {n m : Nat} (h1 h2 : m < n) :
    fresV (n := n) (m := m) h1 = fresV (n := n) (m := m) h2 := by
  have h : (⟨m, h1⟩ : Fin n) = ⟨m, h2⟩ := Fin.ext rfl
  exact Subtype.ext (congrArg Sum.inr h)

theorem fresV_bit_congr {n m : Nat} (w : Asg n m) (h1 h2 : m < n) :
    w (fresV (n := n) (m := m) h1) = w (fresV (n := n) (m := m) h2) := by
  rw [fresV_congr h1 h2]

/-! ### Start-state membership -/

theorem startST_mem_fst (n j : Nat) (w : Asg n j) (k : Nat) :
    k ∈ (startST n j w).1 ↔ k = j := by
  simp [startST]

theorem startST_mem_snd (n j : Nat) (w : Asg n j) (k : Nat) :
    k ∈ (startST n j w).2 ↔ (k = j ∧ ∃ hj : j < n, w (fresV (n := n) (m := j) hj) = true) := by
  unfold startST
  split
  · rename_i hj
    by_cases hbit : w (fresV (n := n) (m := j) hj) = true
    · rw [ite_eq_left hbit]
      constructor
      · intro h
        rcases Finset.mem_insert.1 h with hk | hk
        · exact ⟨hk, ⟨hj, hbit⟩⟩
        · exact absurd hk (Finset.notMem_empty k)
      · intro h; exact Finset.mem_insert.2 (Or.inl h.1)
    · rw [ite_eq_right hbit]
      constructor
      · intro h; exact absurd h (Finset.notMem_empty k)
      · rintro ⟨-, hj', hbit'⟩
        have hh := fresV_bit_congr w hj' hj
        rw [hh] at hbit'
        exact absurd hbit' hbit
  · rename_i hn
    constructor
    · intro h; exact absurd h (Finset.notMem_empty k)
    · rintro ⟨-, hj, -⟩
      exact absurd hj hn

theorem startST_mem (n j : Nat) (w : Asg n j) (k : Nat) (σ : Bool) :
    k ∈ sval σ (startST n j w) ↔
      (k = j ∧ (σ = false ∨ (σ = true ∧ ∃ hj : j < n, w (fresV (n := n) (m := j) hj) = true))) := by
  cases σ with
  | false =>
      have hs : sval false (startST n j w) = (startST n j w).1 := rfl
      rw [hs, startST_mem_fst]
      simp
  | true =>
      have hs : sval true (startST n j w) = (startST n j w).2 := rfl
      rw [hs, startST_mem_snd]
      simp

/-! ### Same-index reachability -/

/-- Reachability between the two copies of one index: reflexivity gives the
same layer, and the opposite layer is reachable exactly when the single shared
vertical token is retained. -/
theorem reach_same_index (n : Nat) (ω : Out n) (u : Fin n) (σ : Bool) :
    Reach n ω (u, false) (u, σ) ↔ (σ = false ∨ ω (vtok u) = true) := by
  constructor
  · intro h
    have key : ∀ b : Vert n, Reach n ω (u, false) b → (b.1 : Nat) = (u : Nat) →
        (b = (u, false) ∨ ω (vtok u) = true) := by
      intro b hb
      induction hb with
      | refl => intro _; exact Or.inl rfl
      | @tail b c h1 h2 ih =>
          intro hc
          have hb1 : (b.1 : Nat) = (u : Nat) := by
            have h1le : (u : Nat) ≤ (b.1 : Nat) := reach_ge h1
            have h2le : (b.1 : Nat) ≤ (c.1 : Nat) := arc_fst_le h2
            omega
          rcases ih hb1 with hbe | hvt
          · subst hbe
            rcases arc_cases h2 with ⟨hce, hlt, hbit⟩ | ⟨hce, hne, hbit⟩
            · exfalso
              omega
            · exact Or.inr hbit
          · exact Or.inr hvt
    rcases key (u, σ) h rfl with h | h
    · have hσ : σ = false := by
        have := congrArg Prod.snd h
        simpa using this
      exact Or.inl hσ
    · exact Or.inr h
  · rintro (hσ | hvt)
    · subst hσ
      exact Relation.ReflTransGen.refl
    · cases σ with
      | false => exact Relation.ReflTransGen.refl
      | true => exact Relation.ReflTransGen.single (arc_vert (l := false) hvt)

/-! ### New-index indicator membership -/

theorem stepU_new_ind_fst (m : Nat) (R S : Finset Nat) (x y z : Bool) (hmR : ¬ m ∈ R) :
    m ∈ (stepU m R S x y z).1 ↔ (ind x y z).1 = true := by
  have h1 : (stepU m R S x y z).1 = if (ind x y z).1 then insert m R else R := rfl
  rw [h1, mem_update_self]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hmR
  · intro h; exact Or.inl h

theorem stepU_new_ind_snd (m : Nat) (R S : Finset Nat) (x y z : Bool) (hmS : ¬ m ∈ S) :
    m ∈ (stepU m R S x y z).2 ↔ (ind x y z).2 = true := by
  have h2 : (stepU m R S x y z).2 = if (ind x y z).2 then insert m S else S := rfl
  rw [h2, mem_update_self]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hmS
  · intro h; exact Or.inl h

end Bun
