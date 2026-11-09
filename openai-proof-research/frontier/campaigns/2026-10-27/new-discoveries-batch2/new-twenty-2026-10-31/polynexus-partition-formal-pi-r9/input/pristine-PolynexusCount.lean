import PolynexusPairs

/-!
# Operand cardinality (MathDB 352496)

The number `T n` of nonzero source matrices equals the number of legal
triples, and satisfies the exact quadratic law `6 * T n = n * (n+1) * (2*n+1)`.
No enumeration and no truncated-substitution proxy: the cardinality is the
actual `Finset.card` of the actual nonzero-matrix set, partitioned by the
third triple entry.
-/

/-- The `e`-fiber of `PLeg n`: legal triples whose third entry is `e`. -/
def PLegFib (n e : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n - e) ×ˢ Finset.range (n - e)).image fun ab => (ab.1, ab.2, e)

theorem PLegFib_mem {n e : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ PLegFib n e ↔ t.2.2 = e ∧ t.1 < n - e ∧ t.2.1 < n - e := by
  constructor
  · rintro ⟨ab, hab, habeq⟩
    obtain ⟨hab1, hab2⟩ := Finset.mem_product.1 hab
    have h22 : t.2.2 = e := by rw [← habeq]
    have h11 : t.1 = ab.1 := by rw [← habeq]
    have h21 : t.2.1 = ab.2 := by rw [← habeq]
    exact ⟨h22, by rw [h11]; exact Finset.mem_range.1 hab1,
      by rw [h21]; exact Finset.mem_range.1 hab2⟩
  · rintro ⟨he, h1, h2⟩
    refine ⟨(t.1, t.2.1), Finset.mem_product.2 ⟨Finset.mem_range.2 h1,
      Finset.mem_range.2 h2⟩, ?_⟩
    rw [← he]

theorem PLegFib_card (n e : ℕ) : (PLegFib n e).card = (n - e) ^ 2 := by
  have hinj : Function.Injective fun ab : ℕ × ℕ => (ab.1, ab.2, e) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    injection h with h1 h23
    injection h23 with h2 _
    exact by rw [h1, h2]
  rw [PLegFib, Finset.card_image_of_injective _ hinj, Finset.card_product,
    Finset.card_range, Finset.card_range]

theorem PLeg_card (n : ℕ) : (PLeg n).card = ∑ e ∈ Finset.range n, (n - e) ^ 2 := by
  have hd : ∀ (u v : ℕ), u ≠ v → Disjoint (PLegFib n u) (PLegFib n v) := by
    intro u v huv
    refine Finset.disjoint_left.2 fun t h1 h2 => ?_
    have e1 := (PLegFib_mem.1 h1).1
    have e2 := (PLegFib_mem.1 h2).1
    have huv' : u = v := by rw [← e1, ← e2]
    exact huv huv'
  have hPL : PLeg n = (Finset.range n).biUnion (PLegFib n) := rfl
  have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint (PLegFib n) := by
    intro u hu v hv huv
    exact hd u v huv
  rw [hPL, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun e _ => PLegFib_card n e

theorem rangeOne (k : ℕ) : ∑ _i ∈ Finset.range k, (1 : ℕ) = k := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- The linear fiber-sum law `2 * ∑_{i<n} (n-i) = n * (n+1)`. -/
theorem legLin (n : ℕ) : 2 * ∑ i ∈ Finset.range n, (n - i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have pt : ∑ i ∈ Finset.range m, (m + 1 - i)
        = (∑ i ∈ Finset.range m, (m - i)) + m := by
      have t : ∑ i ∈ Finset.range m, (m + 1 - i)
          = ∑ i ∈ Finset.range m, ((m - i) + 1) :=
        Finset.sum_congr rfl fun i hi => by
          have him : i < m := Finset.mem_range.1 hi
          omega
      rw [t, Finset.sum_add_distrib, rangeOne]
    have e1 : ∑ i ∈ Finset.range (m + 1), (m + 1 - i)
        = (∑ i ∈ Finset.range m, (m - i)) + (m + 1) := by
      rw [Finset.sum_range_succ, pt]; omega
    have eX : (∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i))
        = m * (m + 1) := by
      rw [← legLin m]; ring
    have dist : 2 * ((∑ i ∈ Finset.range m, (m - i)) + (m + 1))
        = 2 * ∑ i ∈ Finset.range m, (m - i) + 2 * (m + 1) := by ring
    rw [e1, dist, ih]; ring

/-- The quadratic fiber-sum law `6 * ∑_{i<n} (n-i)^2 = n (n+1) (2n+1)`. -/
theorem legSq (n : ℕ) :
    6 * ∑ i ∈ Finset.range n, (n - i) ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have pt : ∑ i ∈ Finset.range m, (m + 1 - i) ^ 2
        = (∑ i ∈ Finset.range m, (m - i) ^ 2)
          + ((∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i))) + m := by
      have t : ∑ i ∈ Finset.range m, (m + 1 - i) ^ 2
          = ∑ i ∈ Finset.range m, ((m - i) ^ 2 + ((m - i) + (m - i)) + 1) :=
        Finset.sum_congr rfl fun i hi => by
          have him : i < m := Finset.mem_range.1 hi
          rw [show m + 1 - i = m - i + 1 from by omega]
          ring
      rw [t, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        rangeOne]
    have e1 : ∑ i ∈ Finset.range (m + 1), (m + 1 - i) ^ 2
        = (∑ i ∈ Finset.range m, (m - i) ^ 2)
          + ((∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i)))
          + (m + 1) := by
      rw [Finset.sum_range_succ, pt]; ring
    have eX : (∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i))
        = m * (m + 1) := by
      rw [← legLin m]; ring
    have dist : 6 * ((∑ i ∈ Finset.range m, (m - i) ^ 2)
          + (((∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i)))
            + (m + 1)))
        = 6 * ∑ i ∈ Finset.range m, (m - i) ^ 2
          + 6 * (((∑ i ∈ Finset.range m, (m - i)) + (∑ i ∈ Finset.range m, (m - i))))
          + 6 * (m + 1) := by ring
    rw [e1, dist, eX, ih]; ring

/-- The nonzero-block cardinality equals the legal-triple cardinality. -/
theorem PNZ_card (n : ℕ) : (PNZ n).card = (PLeg n).card := by
  rw [PNZ, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  exact PB_inj (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hy) hxy

/-- The exact quadratic law for the number `T n` of nonzero source matrices. -/
theorem PNZ_card_sq (n : ℕ) :
    6 * (PNZ n).card = n * (n + 1) * (2 * n + 1) := by
  rw [PNZ_card, PLeg_card, legSq]
