import PolynexusDiag

/-!
# Source one-based signed model and the parameter dictionary (MathDB 352496)

The source matrices are `X(d,k,m)` with signed shift `d : ℤ` and one-based
indices: entry `1` iff `k ≤ i ≤ m` and `j = i + d`, legality
`1 ≤ k ≤ m ≤ n`, `1 ≤ k+d`, `m+d ≤ n`.  This module proves the exact
dictionary to the zero-based coupled blocks: `(a,b,e) = (k-1, k+d-1, m-k)`
with inverse `k = a+1, m = a+e+1, d = b-a`, entrywise agreement of the
actual matrices, uniqueness of parameters on both sides (injectivity), and
that legal source matrices are nonzero.
-/

/-- Source legality with the printed one-based bounds, signed shift. -/
def PSrcLeg (n : ℕ) (d : ℤ) (k m : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ m ∧ m ≤ n ∧ 1 ≤ (k:ℤ) + d ∧ (m:ℤ) + d ≤ (n:ℤ)

/-- The source one-based rook-diagonal matrix `X(d,k,m)` on `Fin n`:
entry `1` exactly on one diagonal segment. -/
def PSrc (n : ℕ) (d : ℤ) (k m : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) then 1 else 0

theorem PSrc_apply (n : ℕ) (d : ℤ) (k m : ℕ) (i j : Fin n) :
    PSrc n d k m i j =
      if (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) then 1 else 0 :=
  rfl

/-- Zero-based dictionary entries. -/
abbrev srcA (k : ℕ) : ℕ := k - 1

/-- `b = k+d-1` as a natural; legal source triples make the cast exact. -/
def srcB (d : ℤ) (k : ℕ) : ℕ := ((k:ℤ) + d - 1).toNat

abbrev srcE (k m : ℕ) : ℕ := m - k

theorem srcB_cast {d : ℤ} {k : ℕ} (h : 1 ≤ (k:ℤ) + d) :
    ((srcB d k : ℕ) : ℤ) = (k:ℤ) + d - 1 := by
  have h0 : 0 ≤ (k:ℤ) + d - 1 := by omega
  exact Int.toNat_of_nonneg h0

/-- Entry value of the source matrix at bounded natural coordinates. -/
theorem PSrc_entry_nat (n : ℕ) (d : ℤ) (k m r s : ℕ) (hr : r < n) (hs : s < n) :
    PSrc n d k m ⟨r, hr⟩ ⟨s, hs⟩ =
      if (k ≤ r + 1 ∧ r + 1 ≤ m ∧ (s:ℤ) + 1 = (r:ℤ) + 1 + d) then 1 else 0 := by
  show (if (k ≤ (⟨r, hr⟩ : Fin n).val + 1 ∧ (⟨r, hr⟩ : Fin n).val + 1 ≤ m
        ∧ ((⟨s, hs⟩ : Fin n) : ℤ) + 1 = (⟨r, hr⟩ : Fin n).val + 1 + d) then 1 else 0)
      = (if (k ≤ r + 1 ∧ r + 1 ≤ m ∧ (s:ℤ) + 1 = (r:ℤ) + 1 + d) then 1 else 0)
  congr 1

/-- Source entry is `1` at the one-based coupled condition (Fin form). -/
theorem PSrc_one {n : ℕ} {d : ℤ} {k m : ℕ} {i j : Fin n}
    (h : k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) :
    PSrc n d k m i j = 1 := by
  show (if (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) then 1 else 0) = 1
  exact ite_eq_left h

theorem PSrc_zero {n : ℕ} {d : ℤ} {k m : ℕ} {i j : Fin n}
    (h : ¬ (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d)) :
    PSrc n d k m i j = 0 := by
  show (if (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) then 1 else 0) = 0
  exact ite_eq_right h

/-- The exact condition bridge in plain natural parameters: the source
one-based condition iff the zero-based coupled `PCnd` with `a = k-1`,
`b` any natural realizing `k+d-1`, `e = m-k`. -/
theorem srcCond_iff_PCnd {n : ℕ} {d : ℤ} {k m b : ℕ} (h : PSrcLeg n d k m)
    (r s : ℕ) (hb : (b:ℤ) = (k:ℤ) + d - 1) :
    (k ≤ r + 1 ∧ r + 1 ≤ m ∧ (s:ℤ) + 1 = (r:ℤ) + 1 + d) ↔
      PCnd (k - 1) b (m - k) r s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  constructor
  · rintro ⟨hc1, hc2, hc3⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega
  · rintro ⟨c1, c2, c3, c4, c5⟩
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega

/-- Legal source matrices are exactly the coupled blocks: the actual matrix
equality `X(d,k,m) = B(k-1, k+d-1, m-k)` at every entry. -/
theorem PSrc_eq_PBlk {n : ℕ} {d : ℤ} {k m : ℕ} (h : PSrcLeg n d k m) :
    PSrc n d k m = PBlk n (srcA k) (srcB d k) (srcE k m) := by
  have hb : ((srcB d k : ℕ) : ℤ) = (k:ℤ) + d - 1 := srcB_cast h.2.2.2.1
  funext i j
  by_cases hc : PCnd (srcA k) (srcB d k) (srcE k m) (i:ℕ) (j:ℕ)
  · have hc' : PCnd (k - 1) (srcB d k) (m - k) (i:ℕ) (j:ℕ) := hc
    rw [PBlk_eq_one hc, PSrc_one
      ((srcCond_iff_PCnd h _ _ hb).2 hc')]
  · have hc' : ¬ PCnd (k - 1) (srcB d k) (m - k) (i:ℕ) (j:ℕ) := hc
    have hbr : (k ≤ (i:ℕ) + 1 ∧ (i:ℕ) + 1 ≤ m ∧ (j:ℤ) + 1 = (i:ℕ) + 1 + d) →
        PCnd (k - 1) (srcB d k) (m - k) (i:ℕ) (j:ℕ) :=
      (srcCond_iff_PCnd h _ _ hb).1
    rw [PBlk_eq_zero hc, PSrc_zero (fun hc'' => hc' (hbr hc''))]

/-- The dictionary lands in legal triples. -/
theorem srcDict_leg {n : ℕ} {d : ℤ} {k m : ℕ} (h : PSrcLeg n d k m) :
    srcA k + srcE k m + 1 ≤ n ∧ srcB d k + srcE k m + 1 ≤ n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hb : ((srcB d k : ℕ) : ℤ) = (k:ℤ) + d - 1 := srcB_cast h4
  have hA : ((srcA k : ℕ) : ℤ) = (k:ℤ) - 1 := Nat.cast_sub (by omega)
  have hE : ((srcE k m : ℕ) : ℤ) = (m:ℤ) - (k:ℤ) := Nat.cast_sub h2
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-- The inverse dictionary is a legal source triple. -/
theorem PSrcLeg_of_leg {n a b e : ℕ} (h : a + e + 1 ≤ n ∧ b + e + 1 ≤ n) :
    PSrcLeg n ((b:ℤ) - (a:ℤ)) (a + 1) (a + e + 1) := by
  have ha : 0 ≤ (a:ℤ) := Int.natCast_nonneg a
  have hb : 0 ≤ (b:ℤ) := Int.natCast_nonneg b
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · omega
  · omega

/-- The inverse dictionary recovers the block: every legal block is a source
matrix, `B(a,b,e) = X(b-a, a+1, a+e+1)`. -/
theorem PBlk_eq_PSrc {n a b e : ℕ} (h : a + e + 1 ≤ n ∧ b + e + 1 ≤ n) :
    PBlk n a b e = PSrc n ((b:ℤ) - (a:ℤ)) (a + 1) (a + e + 1) := by
  have hsrc : PSrc n ((b:ℤ) - (a:ℤ)) (a + 1) (a + e + 1)
      = PBlk n (srcA (a + 1)) (srcB ((b:ℤ) - (a:ℤ)) (a + 1)) (srcE (a + 1) (a + e + 1)) :=
    PSrc_eq_PBlk (PSrcLeg_of_leg h)
  have hA : srcA (a + 1) = a := rfl
  have hE : srcE (a + 1) (a + e + 1) = e := by
    show a + e + 1 - (a + 1) = e
    omega
  have hB : srcB ((b:ℤ) - (a:ℤ)) (a + 1) = b := by
    refine Nat.cast_injective (R := ℤ) ?_
    have hc : ((srcB ((b:ℤ) - (a:ℤ)) (a + 1) : ℕ) : ℤ)
        = ((a + 1 : ℕ) : ℤ) + ((b:ℤ) - (a:ℤ)) - 1 :=
      srcB_cast (PSrcLeg_of_leg h).2.2.2.1
    omega
  rw [hsrc, hA, hE, hB]

/-- Uniqueness of block parameters: on legal triples the map
`(a,b,e) ↦ B(a,b,e)` is injective.  Only occupied coupled entries are used
(the start corner and the far diagonal corner), never a rectangle lemma. -/
theorem PBlk_inj {n : ℕ} {a b e a' b' e' : ℕ}
    (h : a + e + 1 ≤ n ∧ b + e + 1 ≤ n) (h' : a' + e' + 1 ≤ n ∧ b' + e' + 1 ≤ n)
    (hmat : PBlk n a b e = PBlk n a' b' e') : a = a' ∧ b = b' ∧ e = e' := by
  have hlt1 : a < n := by omega
  have hlt2 : b < n := by omega
  have hlt3 : a + e < n := by omega
  have hlt4 : b + e < n := by omega
  have hlt1' : a' < n := by omega
  have hlt2' : b' < n := by omega
  have hlt3' : a' + e' < n := by omega
  have hlt4' : b' + e' < n := by omega
  have e1 : PBlk n a' b' e' ⟨a, hlt1⟩ ⟨b, hlt2⟩ = 1 := by
    rw [← hmat]; exact PBlk_corner_one hlt1 hlt2
  have e2 : PBlk n a b e ⟨a', hlt1'⟩ ⟨b', hlt2'⟩ = 1 := by
    rw [hmat]; exact PBlk_corner_one hlt1' hlt2'
  have e3 : PBlk n a' b' e' ⟨a + e, hlt3⟩ ⟨b + e, hlt4⟩ = 1 := by
    rw [← hmat]; exact PBlk_occupied_one (Nat.le_refl e) hlt3 hlt4
  have e4 : PBlk n a b e ⟨a' + e', hlt3'⟩ ⟨b' + e', hlt4'⟩ = 1 := by
    rw [hmat]; exact PBlk_occupied_one (Nat.le_refl e') hlt3' hlt4'
  have c1 := (PBlk_one_iff_nat n a' b' e' a b hlt1 hlt2).1 e1
  have c2 := (PBlk_one_iff_nat n a b e a' b' hlt1' hlt2').1 e2
  have c3 := (PBlk_one_iff_nat n a' b' e' (a + e) (b + e) hlt3 hlt4).1 e3
  have c4 := (PBlk_one_iff_nat n a b e (a' + e') (b' + e') hlt3' hlt4').1 e4
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Uniqueness of source parameters: on legal source triples `(d,k,m)` the
matrix determines the triple. -/
theorem PSrc_inj {n : ℕ} {d d' : ℤ} {k m k' m' : ℕ}
    (h : PSrcLeg n d k m) (h' : PSrcLeg n d' k' m')
    (hmat : PSrc n d k m = PSrc n d' k' m') : d = d' ∧ k = k' ∧ m = m' := by
  have hb : PBlk n (srcA k) (srcB d k) (srcE k m)
      = PBlk n (srcA k') (srcB d' k') (srcE k' m') := by
    rw [← PSrc_eq_PBlk h, ← PSrc_eq_PBlk h', hmat]
  have hd := PBlk_inj (srcDict_leg h) (srcDict_leg h') hb
  obtain ⟨ha, hb', he⟩ := hd
  have hA : ((srcA k : ℕ) : ℤ) = (k:ℤ) - 1 := Nat.cast_sub h.1
  have hA' : ((srcA k' : ℕ) : ℤ) = (k':ℤ) - 1 := Nat.cast_sub h'.1
  have hE : ((srcE k m : ℕ) : ℤ) = (m:ℤ) - (k:ℤ) := Nat.cast_sub h.2.1
  have hE' : ((srcE k' m' : ℕ) : ℤ) = (m':ℤ) - (k':ℤ) := Nat.cast_sub h'.2.1
  refine ⟨?_, ?_, ?_⟩
  · have hc : ((srcB d k : ℕ) : ℤ) = (k:ℤ) + d - 1 := srcB_cast h.2.2.2.1
    have hc' : ((srcB d' k' : ℕ) : ℤ) = (k':ℤ) + d' - 1 := srcB_cast h'.2.2.2.1
    omega
  · omega
  · omega

/-- Legal source matrices are nonzero, witnessed by the start entry `(k, k+d)`. -/
theorem PSrc_ne_zero {n : ℕ} {d : ℤ} {k m : ℕ} (h : PSrcLeg n d k m) :
    PSrc n d k m ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hA : srcA k = k - 1 := rfl
  have hlt : srcA k < n := by omega
  have hb : ((srcB d k : ℕ) : ℤ) = (k:ℤ) + d - 1 := srcB_cast h4
  have hAc : ((srcA k : ℕ) : ℤ) = (k:ℤ) - 1 := Nat.cast_sub h1
  have hltB : srcB d k < n := by omega
  intro hcon
  have e1 : PSrc n d k m ⟨srcA k, hlt⟩ ⟨srcB d k, hltB⟩ = 1 := by
    refine PSrc_one ?_
    refine ⟨?_, ?_, ?_⟩
    · show k ≤ (srcA k : ℕ) + 1
      omega
    · show (srcA k : ℕ) + 1 ≤ m
      omega
    · show (srcB d k : ℕ) + 1 = (srcA k : ℕ) + 1 + d
      omega
  rw [hcon, Matrix.zero_apply] at e1
  omega
