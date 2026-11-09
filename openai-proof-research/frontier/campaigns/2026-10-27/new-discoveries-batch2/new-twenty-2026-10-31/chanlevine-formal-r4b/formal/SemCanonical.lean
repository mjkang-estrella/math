import SourceSemantics
namespace ChanLevine
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem canonical_cycleTest (hn : 3 ≤ n) {m : ℕ} (hm : 1 ≤ m) (i : ZMod n) :
    CycleTest (canonical m i) := by
  have hz : (canonical m i).x 0 ≠ 0 := by simp [canonical]; omega
  refine ⟨?_, (fun _ => ⟨0, hz⟩), (fun _ => ⟨0, hz⟩)⟩
  intro k hk hk1
  by_cases h0 : k = 0
  · exact Or.inl (h0 ▸ hz)
  have hp : ¬ (1 ≤ k.val ∧ k.val ≤ i.val) := by
    have h : k = 0 ∨ i.val < k.val := by simpa [canonical] using hk
    rcases h with h | h
    · exact False.elim (h0 h)
    · omega
  have hp1 : 1 ≤ (k+1).val ∧ (k+1).val ≤ i.val := by
    simpa [canonical] using hk1
  have hv : 1 ≤ k.val := by
    have := (ZMod.val_eq_zero k).not.mpr h0
    omega
  have hi := ZMod.val_lt i
  have hklt := ZMod.val_lt k
  have hone : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  rw [ZMod.val_add, hone] at hp1
  have hnz : n ≠ 0 := NeZero.ne n
  by_cases hwrap : k.val + 1 < n
  · rw [Nat.mod_eq_of_lt hwrap] at hp1
    omega
  · have he : k.val + 1 = n := by omega
    simp [he] at hp1

theorem canonical_weight (m : ℕ) (i : ZMod n) : chipWeight (canonical m i) = i := by
  unfold chipWeight weight Config.lift canonical
  simp only [Int.cast_natCast]
  have hchips : (∑ k : ZMod n, k * ((if k = 0 then m else 0 : ℕ) : ZMod n)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with h <;> simp [h]
  rw [hchips, zero_add]
  have heq : ∀ k : ZMod n, (if (if 1 ≤ k.val ∧ k.val ≤ i.val then false else true) = true then (0 : ZMod n) else 1) = (if 1 ≤ k.val ∧ k.val ≤ i.val then 1 else 0) := by
    intro k
    split_ifs <;> simp_all
  simp_rw [heq]
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
    change (∑ k : Fin (n+1), if 1 ≤ k.val ∧ k.val ≤ i.val then (1 : ZMod (n+1)) else 0) = i
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if 1 ≤ k ∧ k ≤ i.val then (1 : ZMod (n+1)) else 0)]
    have he : (∑ k ∈ Finset.range (n+1), if 1 ≤ k ∧ k ≤ i.val then (1 : ZMod (n+1)) else 0) = i.val := by
      rw [← Finset.sum_filter]
      have hf : (Finset.range (n+1)).filter (fun k => 1 ≤ k ∧ k ≤ i.val) = Finset.Icc 1 i.val := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        have := ZMod.val_lt i
        omega
      rw [hf]
      simp
    exact he.trans (ZMod.natCast_zmod_val i)
end ChanLevine
