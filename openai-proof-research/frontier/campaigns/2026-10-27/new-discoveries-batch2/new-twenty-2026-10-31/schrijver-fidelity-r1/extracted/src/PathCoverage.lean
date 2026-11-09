import PathGenerator
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem validMask_path_cover {n k m : ℕ} (hm : validMask n k m = true) :
    m ∈ pathMasks n k := by
  classical
  obtain ⟨hbound, hcard, hstable⟩ := validMask_sound hm
  let s : Finset ℕ := (decode n m).image Fin.val
  have hb : ∀ a ∈ s, a < n := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact i.isLt
  have hc : s.card = k := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    exact hcard
  have hs : ∀ a ∈ s, a + 1 ∉ s := by
    intro a ha hnext
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp hnext
    apply hstable i hi j hj
    rw [hia, ← hja, Nat.mod_eq_of_lt j.isLt]
  have he : encodeList s.toList = m := by
    apply Nat.eq_of_testBit_eq
    intro a
    rw [encodeList_bit]
    by_cases ha : a < n
    · have hx : a ∈ s ↔ m.testBit a = true := by
        simp only [s, Finset.mem_image, decode, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro h; exact ⟨⟨a, ha⟩, h, rfl⟩
      simp only [Finset.mem_toList, hx, Bool.decide_coe]
    · have hlt : m < 2^a := hbound.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      have hnot : a ∉ s := by intro h; have := hb a h; omega
      simp [hnot, Nat.testBit_lt_two_pow hlt]
  simpa [hc, he] using pathMasks_cover n s hb hs

noncomputable def cyclicMasks (n k : ℕ) : List ℕ :=
  (pathMasks n k).filter (validMask n k)

theorem cyclicMasks_complete {n k m : ℕ} :
    m ∈ cyclicMasks n k ↔ m ∈ referenceMasks n k := by
  rw [referenceMasks_complete]
  simp only [cyclicMasks, List.mem_filter]
  exact ⟨And.right, fun h => ⟨validMask_path_cover h, h⟩⟩
end Schrijver
namespace Schrijver

noncomputable def endMasks (n k : ℕ) : List ℕ :=
  (pathMasks n k).filter (fun m => !(m.testBit 0 && m.testBit (n-1)))

theorem validMask_end_cover {n k m : ℕ} (hn : 0 < n)
    (hm : validMask n k m = true) : m ∈ endMasks n k := by
  apply List.mem_filter.mpr
  refine ⟨validMask_path_cover hm, ?_⟩
  have hs := (validMask_sound hm).2.2
  by_cases ha : m.testBit (n-1) = true
  · have hz : m.testBit 0 ≠ true := by
      intro hz
      apply hs ⟨n-1, by omega⟩ (by simp [decode, ha]) ⟨0, hn⟩ (by simp [decode, hz])
      simp [Nat.sub_add_cancel hn]
    simp [ha, hz]
  · simp [ha]
end Schrijver
