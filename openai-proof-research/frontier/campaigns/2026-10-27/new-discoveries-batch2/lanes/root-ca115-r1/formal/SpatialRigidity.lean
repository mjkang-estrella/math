import ColumnCertificate
set_option autoImplicit false
namespace CA115

theorem bits_bg_iff : ∀ i : Fin 31, bits i = bg ↔ i = ⟨6, by decide⟩ := by
  decide +kernel

theorem fw_from_left (f : ℤ → Fin 31) (L : ℤ)
    (hl : ∀ z, z ≤ L + 1 → f z = ⟨6, by decide⟩)
    (h : ∀ z, RawLegal (bits (f (z-1))) (bits (f z)) (bits (f (z+1)))) :
    ∀ z, FW (f z) (f (z+1)) := by
  have hn : ∀ n : ℕ, FW (f (L+n)) (f (L+n+1)) := by
    intro n
    induction n with
    | zero => simpa [hl L (by omega), hl (L+1) (by omega)] using forward_root
    | succ n ih =>
      have he := forward_closed _ _ _ ih (by simpa only [add_sub_cancel_right] using h (L+n+1))
      convert he using 1 <;> congr 1 <;> omega
  intro z
  by_cases hz : z ≤ L
  · simpa [hl z (by omega), hl (z+1) (by omega)] using forward_root
  · have he := hn (z-L).toNat
    convert he using 1 <;> congr 1 <;> omega

theorem bw_from_right (f : ℤ → Fin 31) (R : ℤ)
    (hr : ∀ z, R ≤ z → f z = ⟨6, by decide⟩)
    (h : ∀ z, RawLegal (bits (f (z-1))) (bits (f z)) (bits (f (z+1)))) :
    ∀ z, BW (f z) (f (z+1)) := by
  have hn : ∀ n : ℕ, BW (f (R-n)) (f (R-n+1)) := by
    intro n
    induction n with
    | zero => simpa [hr R (by omega), hr (R+1) (by omega)] using backward_root
    | succ n ih =>
      have he := backward_closed _ _ _ ih (h (R-n))
      convert he using 1 <;> congr 1 <;> omega
  intro z
  by_cases hz : R ≤ z
  · simpa [hr z (by omega), hr (z+1) (by omega)] using backward_root
  · have he := hn (R-z).toNat
    convert he using 1 <;> congr 1 <;> omega

theorem finite_column_rigidity (c : ℤ → RawColumn)
    (hlegal : ∀ z, RawLegal (c (z-1)) (c z) (c (z+1)))
    (hfinite : ∃ R : ℕ, ∀ z, z ≤ -(R:ℤ) ∨ (R:ℤ) ≤ z → c z = bg) :
    ∀ z, c z = bg ∨ c z = allOne := by
  classical
  choose f hf using fun z => valid_enumeration (c z) (legal_valid _ _ _ (hlegal z))
  have he : ∀ z, RawLegal (bits (f (z-1))) (bits (f z)) (bits (f (z+1))) := by
    intro z
    simpa only [hf] using hlegal z
  obtain ⟨R, hR⟩ := hfinite
  have hl : ∀ z, z ≤ -(R:ℤ)-1 → f z = ⟨6, by decide⟩ := by
    intro z hz
    apply (bits_bg_iff _).mp
    rw [hf]
    exact hR z (Or.inl (by omega))
  have hr : ∀ z, (R:ℤ) ≤ z → f z = ⟨6, by decide⟩ := by
    intro z hz
    apply (bits_bg_iff _).mp
    rw [hf]
    exact hR z (Or.inr hz)
  have hfw := fw_from_left f (-(R:ℤ)-2) (by intro z hz; apply hl; omega) he
  have hbw := bw_from_right f R hr he
  intro z
  have hc := core_columns (f (z-1)) (f z)
  have hfw' : FW (f (z-1)) (f z) := by simpa only [sub_add_cancel] using hfw (z-1)
  have hbw' : BW (f (z-1)) (f z) := by simpa only [sub_add_cancel] using hbw (z-1)
  simpa only [hf] using hc hfw' hbw'

end CA115
