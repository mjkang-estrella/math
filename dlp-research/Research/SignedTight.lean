import Research.SignedCoverage

/-! Tight cyclic coverage for the known zero-centered signed-block construction.
These are natural/modular arithmetic facts, not an executable group algorithm,
lookup refinement, operation count, runtime bound, or new attack. The existing
experiment and `SignedCoverage.blocks` are unchanged. -/
namespace Research.SignedTight

open Research.SignedCoverage (stride)

def tightBlocks (q m : Nat) : Nat := (q - 1) / stride m + 1

def Matches (q m d i : Nat) : Prop :=
  ∃ j, j < m ∧ ((i * stride m + j) % q = d ∨ (d + j) % q = (i * stride m) % q)

def firstHit (q m d : Nat) : Nat :=
  if d ≤ m - 1 ∨ q ≤ d + (m - 1) then 0
  else (d + (m - 1)) / stride m

theorem stride_radius (m : Nat) (hm : 0 < m) : stride m = 2 * (m - 1) + 1 := by
  unfold stride
  omega

theorem stride_pos (m : Nat) (hm : 0 < m) : 0 < stride m := by
  rw [stride_radius m hm]
  omega

theorem old_blocks_ge_tight (q m : Nat) :
    tightBlocks q m ≤ SignedCoverage.blocks q m := by
  have h : (q - 1) / stride m ≤ (q - 1 + (m - 1)) / stride m :=
    Nat.div_le_div_right (Nat.le_add_right (q - 1) (m - 1))
  unfold tightBlocks SignedCoverage.blocks
  omega

theorem old_blocks_le_tight_succ (q m : Nat) (hm : 0 < m) :
    SignedCoverage.blocks q m ≤ tightBlocks q m + 1 := by
  have hs := stride_pos m hm
  have hr : m - 1 ≤ stride m := by rw [stride_radius m hm]; omega
  have h : (q - 1 + (m - 1)) / stride m ≤ (q - 1 + stride m) / stride m :=
    Nat.div_le_div_right (Nat.add_le_add_left hr (q - 1))
  rw [Nat.add_div_right _ hs] at h
  unfold tightBlocks SignedCoverage.blocks
  omega

theorem old_blocks_eq_or_succ (q m : Nat) (hm : 0 < m) :
    SignedCoverage.blocks q m = tightBlocks q m ∨
      SignedCoverage.blocks q m = tightBlocks q m + 1 := by
  have := old_blocks_ge_tight q m
  have := old_blocks_le_tight_succ q m hm
  omega

/-- The first block covers both the ordinary low interval and its wrapped tail. -/
theorem zero_block_matches (q m d : Nat) (_hq : 0 < q) (hm : 0 < m)
    (hd : d < q) (hnear : d ≤ m - 1 ∨ q ≤ d + (m - 1)) : Matches q m d 0 := by
  rcases hnear with hlow | hwrap
  · refine ⟨d, by omega, Or.inl ?_⟩
    simp [Nat.mod_eq_of_lt hd]
  · refine ⟨q - d, by omega, Or.inr ?_⟩
    have hsum : d + (q - d) = q := by omega
    simp [hsum]

/-- Away from the wrapped tail, the shifted Euclidean quotient is in the
tight cap and has a signed baby magnitude below m. -/
theorem interior_matches (q m d : Nat) (hq : 0 < q) (hm : 0 < m)
    (hd : d < q) (hinterior : d + (m - 1) < q) :
    (d + (m - 1)) / stride m < tightBlocks q m ∧
      Matches q m d ((d + (m - 1)) / stride m) := by
  let t := d + (m - 1)
  let i := t / stride m
  have hs := stride_pos m hm
  have ht : t ≤ q - 1 := by dsimp [t]; omega
  have hi : i < tightBlocks q m := by
    have hdiv : t / stride m ≤ (q - 1) / stride m := Nat.div_le_div_right ht
    dsimp [i, tightBlocks]
    omega
  have hrem : t % stride m < 2 * m - 1 := Nat.mod_lt t hs
  have heq : t % stride m + i * stride m = t := by
    simpa [i, Nat.mul_comm] using Nat.mod_add_div t (stride m)
  refine ⟨hi, ?_⟩
  dsimp [t] at heq hrem
  by_cases hcenter : i * stride m ≤ d
  · refine ⟨d - i * stride m, by omega, Or.inl ?_⟩
    have hdigit : i * stride m + (d - i * stride m) = d := by omega
    rw [hdigit, Nat.mod_eq_of_lt hd]
  · refine ⟨i * stride m - d, by omega, Or.inr ?_⟩
    have hdigit : d + (i * stride m - d) = i * stride m := by omega
    rw [hdigit]

/-- Coverage needs no strict-span hypothesis, even when m exceeds q. -/
theorem firstHit_covers (q m d : Nat) (hq : 0 < q) (hm : 0 < m) (hd : d < q) :
    firstHit q m d < tightBlocks q m ∧ Matches q m d (firstHit q m d) := by
  unfold firstHit
  split
  · rename_i hnear
    exact ⟨Nat.zero_lt_succ _, zero_block_matches q m d hq hm hd hnear⟩
  · rename_i hinterior
    exact interior_matches q m d hq hm hd (by omega)

theorem covers (q m d : Nat) (hq : 0 < q) (hm : 0 < m) (hd : d < q) :
    ∃ i, i < tightBlocks q m ∧ ∃ j, j < m ∧
      ((i * stride m + j) % q = d ∨ (d + j) % q = (i * stride m) % q) := by
  exact ⟨firstHit q m d, firstHit_covers q m d hq hm hd⟩

/-- Every earlier sequential block misses. Wrapped scalars already hit block
zero; in the remaining case neither side of an earlier block can wrap. -/
theorem earlier_blocks_miss (q m d i : Nat) (_hq : 0 < q) (hm : 0 < m)
    (hd : d < q) (hi : i < firstHit q m d) : ¬ Matches q m d i := by
  unfold firstHit at hi
  split at hi
  · omega
  · rename_i hnotnear
    have hupper : d + (m - 1) < q := by omega
    have hdiv : (i + 1) * stride m ≤ d + (m - 1) :=
      (Nat.le_div_iff_mul_le (stride_pos m hm)).mp (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hdiv
    have hs := stride_radius m hm
    have hsmall : i * stride m + (m - 1) < d := by omega
    intro hmatch
    rcases hmatch with ⟨j, hj, hpos | hneg⟩
    · have hab : i * stride m + j < q := by omega
      rw [Nat.mod_eq_of_lt hab] at hpos
      omega
    · have hab : d + j < q := by omega
      have hcenter : i * stride m < q := by omega
      rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hcenter] at hneg
      omega

theorem firstHit_le_of_match (q m d i : Nat) (hq : 0 < q) (hm : 0 < m)
    (hd : d < q) (hmatch : Matches q m d i) : firstHit q m d ≤ i := by
  by_cases h : firstHit q m d ≤ i
  · exact h
  · exact False.elim (earlier_blocks_miss q m d i hq hm hd (by omega) hmatch)

/-- Exact first-hit formula in ascending block order. Strict span is unnecessary
for this arithmetic statement; it is still required by any use of the prior
signed-baby uniqueness lemma, which this theorem does not weaken. -/
theorem firstHit_exact (q m d : Nat) (hq : 0 < q) (hm : 0 < m) (hd : d < q) :
    firstHit q m d < tightBlocks q m ∧
      Matches q m d (firstHit q m d) ∧
      ∀ i, i < firstHit q m d → ¬ Matches q m d i := by
  have hc := firstHit_covers q m d hq hm hd
  exact ⟨hc.1, hc.2, fun i hi => earlier_blocks_miss q m d i hq hm hd hi⟩

/-- Some canonical scalar first matches the final block of the tight cap. -/
theorem last_block_witness (q m : Nat) (hq : 0 < q) (hm : 0 < m) :
    ∃ d, d < q ∧ firstHit q m d = tightBlocks q m - 1 := by
  let b := (q - 1) / stride m
  have hcap : tightBlocks q m - 1 = b := by simp [tightBlocks, b]
  by_cases hb : b = 0
  · refine ⟨0, hq, ?_⟩
    rw [hcap, hb]
    simp [firstHit]
  · have hs := stride_pos m hm
    have hsr := stride_radius m hm
    have hcenter : b * stride m ≤ q - 1 := by
      simpa [b] using Nat.div_mul_le_self (q - 1) (stride m)
    have hsmall : stride m ≤ b * stride m := by
      have h := Nat.mul_le_mul_right (stride m) (show 1 ≤ b by omega)
      simpa using h
    let d := b * stride m - (m - 1)
    have hsum : d + (m - 1) = b * stride m := by dsimp [d]; omega
    have hlow : m - 1 < d := by omega
    have hupper : d + (m - 1) < q := by omega
    have hd : d < q := by omega
    have hfirst : firstHit q m d = b := by
      rw [firstHit, ite_eq_right (by omega), hsum, Nat.mul_div_cancel b hs]
    exact ⟨d, hd, hfirst.trans hcap.symm⟩

/-- Minimal number of sequential centers 0,s,..., not minimality among arbitrary
sets of centers or an algorithm/operation lower bound. -/
theorem sequential_cap_minimal (q m cap : Nat) (hq : 0 < q) (hm : 0 < m)
    (hcoverage : ∀ d, d < q → ∃ i, i < cap ∧ Matches q m d i) :
    tightBlocks q m ≤ cap := by
  rcases last_block_witness q m hq hm with ⟨d, hd, hlast⟩
  rcases hcoverage d hd with ⟨i, hi, hmatch⟩
  have hle := firstHit_le_of_match q m d i hq hm hd hmatch
  have hpositive : 0 < tightBlocks q m := Nat.zero_lt_succ _
  rw [hlast] at hle
  omega

theorem sequential_coverage_iff (q m cap : Nat) (hq : 0 < q) (hm : 0 < m) :
    (∀ d, d < q → ∃ i, i < cap ∧ Matches q m d i) ↔ tightBlocks q m ≤ cap := by
  constructor
  · exact sequential_cap_minimal q m cap hq hm
  · intro hcap d hd
    have hc := firstHit_covers q m d hq hm hd
    exact ⟨firstHit q m d, Nat.lt_of_lt_of_le hc.1 hcap, hc.2⟩

theorem boundary_checks :
    tightBlocks 1 1 = 1 ∧ firstHit 1 1 0 = 0 ∧
    tightBlocks 7 1 = 7 ∧ firstHit 7 1 6 = 6 ∧
    tightBlocks 7 3 = 2 ∧ SignedCoverage.blocks 7 3 = 2 ∧
    firstHit 7 3 3 = 1 ∧ firstHit 7 3 5 = 0 ∧
    tightBlocks 3 2 = 1 ∧ SignedCoverage.blocks 3 2 = 2 ∧
    tightBlocks 2 2 = 1 ∧ firstHit 2 2 1 = 0 ∧
    tightBlocks 7 8 = 1 ∧ firstHit 7 8 6 = 0 ∧
    tightBlocks 10 2 = 4 ∧ firstHit 10 2 8 = 3 ∧ firstHit 10 2 9 = 0 := by
  decide +kernel

end Research.SignedTight
