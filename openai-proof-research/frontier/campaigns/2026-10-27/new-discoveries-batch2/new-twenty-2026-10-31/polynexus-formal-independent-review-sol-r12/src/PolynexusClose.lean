import PolynexusProd

/-!
# Closure of coupled diagonal blocks under ordinary multiplication

With overlap endpoints `H = max b c`, `U = min (b+e) (c+f)`: if `H > U`
the ordinary product is the zero matrix; if `H <= U` the product is the
legal block `B(a+(H-b), q+(H-c), U-H)` at every entry.  Hence the product
is nonzero exactly when `b <= c+f` and `c <= b+e`.  Zero absorption, the
identity block and associativity make the legal blocks with zero a monoid.
-/

/-- Coupled witness and overlapped-output condition agree: under
`b <= c+f` and `c <= b+e`, the witness for entry `(r,k)` is exactly the
coupled condition of the output block `B(A,C,E)`,
`A = a+(max b c - b)`, `C = q+(max b c - c)`, `E = min (b+e) (c+f) - max b c`. -/
theorem PBlk_mul_PCnd_iff {a b e c q f : ℕ} (hov : b ≤ c + f ∧ c ≤ b + e)
    (r k : ℕ) :
    PMulWit a b e c q f r k ↔
      PCnd (a + (max b c - b)) (q + (max b c - c))
        (min (b + e) (c + f) - max b c) r k := by
  have hbH : b ≤ max b c := le_max_left _ _
  have hcH : c ≤ max b c := le_max_right _ _
  have hUe : min (b + e) (c + f) ≤ b + e := min_le_left _ _
  have hUf : min (b + e) (c + f) ≤ c + f := min_le_right _ _
  have hHU : max b c ≤ min (b + e) (c + f) :=
    le_min (max_le (Nat.le_add_right b e) hov.2)
      (max_le hov.1 (Nat.le_add_right c f))
  constructor
  · rintro ⟨u, v, hue, hvf, hr, hj, hk⟩
    have hju : b + u ≤ min (b + e) (c + f) := by
      refine le_min ?_ ?_
      · omega
      · omega
    have hHj : max b c ≤ b + u := by
      refine max_le ?_ ?_
      · omega
      · omega
    refine PCnd_iff_t.2 ⟨b + u - max b c, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · intro hpc
    obtain ⟨w, hw1, hw2, hw3⟩ := PCnd_iff_t.1 hpc
    refine ⟨(max b c - b) + w, (max b c - c) + w, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega

/-- If the middle intervals are disjoint (`b+e < c` or `c+f < b`), the
ordinary product is the zero matrix, entrywise. -/
theorem PBlk_mul_disjoint_zero (n a b e c q f : ℕ)
    (hleg : a + e + 1 ≤ n ∧ b + e + 1 ≤ n ∧ c + f + 1 ≤ n ∧ q + f + 1 ≤ n)
    (hov : ¬ (b ≤ c + f ∧ c ≤ b + e)) :
    PBlk n a b e * PBlk n c q f = 0 := by
  funext r k
  rw [PBlk_mul_entry n a b e c q f hleg r k]
  have hn : ¬ PMulWit a b e c q f (↑r) (↑k) := fun w => hov (PMulWit_overlap w)
  rw [ite_eq_right hn, Matrix.zero_apply]

/-- Overlapping blocks multiply to a legal block: with `H = max b c`,
`U = min (b+e) (c+f)`,
`PBlk a b e * PBlk c q f = PBlk (a+(H-b)) (q+(H-c)) (U-H)` entrywise. -/
theorem PBlk_mul_closure (n a b e c q f : ℕ)
    (hleg : a + e + 1 ≤ n ∧ b + e + 1 ≤ n ∧ c + f + 1 ≤ n ∧ q + f + 1 ≤ n)
    (hov : b ≤ c + f ∧ c ≤ b + e) :
    PBlk n a b e * PBlk n c q f
      = PBlk n (a + (max b c - b)) (q + (max b c - c))
          (min (b + e) (c + f) - max b c) := by
  have hbH : b ≤ max b c := le_max_left _ _
  have hcH : c ≤ max b c := le_max_right _ _
  have hUe : min (b + e) (c + f) ≤ b + e := min_le_left _ _
  have hUf : min (b + e) (c + f) ≤ c + f := min_le_right _ _
  funext r k
  rw [PBlk_mul_entry n a b e c q f hleg r k,
    PBlk_apply n (a + (max b c - b)) (q + (max b c - c))
      (min (b + e) (c + f) - max b c) r k]
  by_cases hQ : PCnd (a + (max b c - b)) (q + (max b c - c))
      (min (b + e) (c + f) - max b c) (↑r) (↑k)
  · rw [ite_eq_left ((PBlk_mul_PCnd_iff hov _ _).2 hQ), ite_eq_left hQ]
  · rw [ite_eq_right (fun w => hQ ((PBlk_mul_PCnd_iff hov _ _).1 w)), ite_eq_right hQ]

/-- The overlapped product block is legal and nonzero: its `A` and `C`
entries are in range and the entry at `(A, C)` is `1`. -/
theorem PBlk_mul_nonzero (n a b e c q f : ℕ)
    (hleg : a + e + 1 ≤ n ∧ b + e + 1 ≤ n ∧ c + f + 1 ≤ n ∧ q + f + 1 ≤ n)
    (hov : b ≤ c + f ∧ c ≤ b + e) :
    PBlk n a b e * PBlk n c q f ≠ 0 := by
  have hbH : b ≤ max b c := le_max_left _ _
  have hcH : c ≤ max b c := le_max_right _ _
  have hUe : min (b + e) (c + f) ≤ b + e := min_le_left _ _
  have hUf : min (b + e) (c + f) ≤ c + f := min_le_right _ _
  have hAE : a + (max b c - b) + (min (b + e) (c + f) - max b c) + 1 ≤ n := by omega
  have hCE : q + (max b c - c) + (min (b + e) (c + f) - max b c) + 1 ≤ n := by omega
  have hAC : a + (max b c - b) < n := by omega
  have hCC : q + (max b c - c) < n := by omega
  intro hcon
  have e1 : (PBlk n a b e * PBlk n c q f)
      ⟨a + (max b c - b), hAC⟩ ⟨q + (max b c - c), hCC⟩ = 1 := by
    rw [PBlk_mul_entry n a b e c q f hleg]
    refine ite_eq_left ⟨max b c - b, max b c - c, ?_, ?_, rfl, ?_, rfl⟩
    · have hH1 : max b c ≤ b + e := max_le (Nat.le_add_right b e) hov.2
      omega
    · have hH2 : max b c ≤ c + f := max_le hov.1 (Nat.le_add_right c f)
      omega
    · have hbH' := hbH
      have hcH' := hcH
      omega
  rw [hcon, Matrix.zero_apply] at e1
  omega

/-- The identity block acts as the multiplicative unit on the left. -/
theorem PBlk_one_mul (n : ℕ) (M : Matrix (Fin n) (Fin n) ℕ) :
    PBlk n 0 0 (n - 1) * M = M := by
  rw [PBlkId, Matrix.one_mul]

/-- The identity block acts as the multiplicative unit on the right. -/
theorem PBlk_mul_one (n : ℕ) (M : Matrix (Fin n) (Fin n) ℕ) :
    M * PBlk n 0 0 (n - 1) = M := by
  rw [PBlkId, Matrix.mul_one]
