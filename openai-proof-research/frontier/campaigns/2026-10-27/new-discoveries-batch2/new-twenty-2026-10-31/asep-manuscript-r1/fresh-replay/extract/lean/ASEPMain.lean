import ASEPBridge
import ASEPCover
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Instances.Real.Lemmas
import ASEPCerts0
import ASEPCerts1
import ASEPCerts2
import ASEPCerts3
import ASEPCerts4
import ASEPCerts5
import ASEPCerts6
import ASEPCerts7
import ASEPCerts8
import ASEPCerts9
import ASEPCerts10
import ASEPCerts11

set_option linter.unusedSimpArgs false

/-!
# Main theorem: the neighborhood-tour conjecture fails at `n = 8`

`x*` (see `ASEPVertex`) is a fractional vertex of `P_ASEP^8` and for every tour `t` the segment
`[x*, t]` is not a face of `P_ASEP^8`; in particular no tour is adjacent to `x*`.
-/

namespace ASEP

open Finset

theorem certs_all : ∀ N ∈ certData, chk (decode N) = true := by
  have h : (certData.all fun N => chk (decode N)) = true := by
    simp only [certData, List.all_append, chunk0_ok, chunk1_ok, chunk2_ok, chunk3_ok, chunk4_ok, chunk5_ok, chunk6_ok, chunk7_ok, chunk8_ok, chunk9_ok, chunk10_ok, chunk11_ok, chunk12_ok, chunk13_ok, chunk14_ok, chunk15_ok, chunk16_ok, chunk17_ok, chunk18_ok, chunk19_ok, chunk20_ok, chunk21_ok, chunk22_ok, chunk23_ok, chunk24_ok, chunk25_ok, chunk26_ok, chunk27_ok, chunk28_ok, chunk29_ok, chunk30_ok, chunk31_ok, chunk32_ok, chunk33_ok, chunk34_ok, chunk35_ok, chunk36_ok, chunk37_ok, chunk38_ok, chunk39_ok, chunk40_ok, chunk41_ok, chunk42_ok, chunk43_ok, chunk44_ok, chunk45_ok, chunk46_ok, chunk47_ok, Bool.and_self]
  exact fun N hN => List.all_eq_true.1 h N hN

theorem finRange8 : List.finRange 8 = (0 : Fin 8) :: l7 := by decide

/-- Every `8`-cycle is the successor map of some certificate. -/
theorem exists_cert (σ : Equiv.Perm (Fin 8)) (hc : σ.IsCycle) (hs : σ.support = Finset.univ) :
    ∃ c : Cert, chk c = true ∧ ∀ i, σ i = c.succ i := by
  have hord : orderOf σ = 8 := by rw [hc.orderOf, hs]; rfl
  have h8 : σ ^ 8 = 1 := by have := pow_orderOf_eq_one σ; rwa [hord] at this
  have hinj : ∀ k l : ℕ, k < 8 → l < 8 → (σ ^ k) 0 = (σ ^ l) 0 → k = l := by
    intro k l hk hl he
    wlog hkl : k ≤ l generalizing k l
    · exact (this l k hl hk he.symm (by omega)).symm
    have hfix : (σ ^ (l - k)) ((σ ^ k) 0) = (σ ^ k) 0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hkl, he]
    have hmem : (σ ^ k) 0 ∈ σ.support := by rw [hs]; exact Finset.mem_univ _
    have hone : σ ^ (l - k) = 1 := (hc.pow_eq_one_iff).2 ⟨(σ ^ k) 0, Equiv.Perm.mem_support.1 hmem, hfix⟩
    have hdvd : orderOf σ ∣ l - k := orderOf_dvd_of_pow_eq_one hone
    rw [hord] at hdvd
    have : l - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  set f : ℕ → Fin 8 := fun k => (σ ^ k) 0 with hf
  set L : List (Fin 8) := (List.range 8).map f with hL
  have hLnd : L.Nodup := by
    rw [hL]; apply List.Nodup.map_on _ List.nodup_range
    intro a ha b hb hab; exact hinj a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab
  have hLlen : L.length = 8 := by simp [hL]
  have hLperm : L.Perm (List.finRange 8) :=
    (List.Nodup.subperm hLnd (fun a _ => List.mem_finRange a)).perm_of_length_le (by simp [hLlen])
  have hLcons : L = 0 :: L.tail := by simp [hL, hf, List.range_succ_eq_map]
  have htlperm : L.tail.Perm l7 := by
    have := hLperm; rw [hLcons, finRange8] at this; exact this.cons_inv
  have hmemP : L.tail ∈ List.permutations' l7 := List.mem_permutations'.2 htlperm
  rw [← certs_cover, List.mem_map] at hmemP
  obtain ⟨N, hN, hNtl⟩ := hmemP
  refine ⟨decode N, certs_all N hN, ?_⟩
  obtain ⟨_, _, _, _, _, _, k7⟩ := chk_spec (certs_all N hN)
  rw [hNtl, ← hLcons] at k7
  have hget : ∀ k, k < 8 → L.getD k 0 = f k := by
    intro k hk; simp [hL, List.getD_eq_getElem?_getD, hk]
  intro i
  have hi : i ∈ L := hLperm.mem_iff.2 (List.mem_finRange i)
  rw [hL, List.mem_map] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  have hk8 := List.mem_range.1 hk
  have := k7 k hk
  rw [hget k hk8, hget _ (Nat.mod_lt _ (by norm_num))] at this
  rw [this]
  simp only [hf]
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  by_cases h7 : k + 1 < 8
  · rw [Nat.mod_eq_of_lt h7]
  · have : k + 1 = 8 := by omega
    rw [this, h8]; simp

/-- No tour is joined to `x*` by a face of `P_ASEP^8`. -/
theorem segment_not_face (t : Fin 8 → Fin 8 → ℝ) (ht : IsTour 8 t) :
    ¬ IsExtreme ℝ (polytope 8) (segment ℝ xs t) := by
  obtain ⟨σ, hc, hs, rfl⟩ := ht
  obtain ⟨c, hchk, hσ⟩ := exists_cert σ hc hs
  have : tourMatrix σ = fun i j => if c.succ i = j then (1 : ℝ) else 0 := by
    funext i j; simp [tourMatrix, hσ i]
  rw [this]; exact not_extreme_of_chk c hchk

/-- The counterexample: a fractional vertex of `P_ASEP^8` adjacent to no tour. -/
theorem counterexample :
    IsVertex 8 xs ∧ xs 0 2 = 1 / 4 ∧ ∀ t, IsTour 8 t → ¬ Adjacent 8 xs t :=
  ⟨xs_extreme, xs_fractional, fun t ht hadj => segment_not_face t ht hadj.2.2.2⟩

/-- The same with faces read as exposed faces (`IsExposed` implies `IsExtreme`). -/
theorem segment_not_exposed (t : Fin 8 → Fin 8 → ℝ) (ht : IsTour 8 t) :
    ¬ IsExposed ℝ (polytope 8) (segment ℝ xs t) :=
  fun h => segment_not_face t ht h.isExtreme

/-- Conjecture 1 of Vercesi–Barta–Gambardella–Gualandi–Mastrolilli (MathDB 368807) is false. -/
theorem neighborhood_tour_conjecture_false : ¬ NeighborhoodTourConjecture := by
  intro h
  obtain ⟨t, ht, hadj⟩ := h 8 (by norm_num) xs xs_extreme
  exact counterexample.2.2 t ht hadj

end ASEP

#print axioms ASEP.counterexample
#print axioms ASEP.neighborhood_tour_conjecture_false
#print axioms ASEP.segment_not_exposed
