import HeadTail

namespace KadarYu

open Matrix Finset Polynomial

theorem multiset_threshold_partition (t : ℝ) (s : Multiset ℝ) :
    (s.filter fun x => t < x).card + (s.filter fun x => x < t).card + s.count t = s.card := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    by_cases hp : t < x
    · have hn : ¬ x < t := by linarith
      rw [Multiset.filter_cons_of_pos (p := fun y : ℝ => t < y) s hp,
        Multiset.filter_cons_of_neg (p := fun y : ℝ => y < t) s hn,
        Multiset.count_cons_of_ne (ne_of_lt hp), Multiset.card_cons, Multiset.card_cons]
      omega
    · by_cases hn : x < t
      · rw [Multiset.filter_cons_of_neg (p := fun y : ℝ => t < y) s hp,
          Multiset.filter_cons_of_pos (p := fun y : ℝ => y < t) s hn,
          Multiset.count_cons_of_ne (Ne.symm (ne_of_lt hn)),
          Multiset.card_cons, Multiset.card_cons]
        omega
      · have he : x = t := by linarith
        subst x
        rw [Multiset.filter_cons_of_neg (p := fun y : ℝ => t < y) s (lt_irrefl t),
          Multiset.filter_cons_of_neg (p := fun y : ℝ => y < t) s (lt_irrefl t),
          Multiset.count_cons_self, Multiset.card_cons]
        omega

theorem spectral_counts_multiplicity {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (t : ℝ) :
    spectralCountAbove hA t + spectralCountBelow hA t + A.charpoly.roots.count t =
      Fintype.card n := by
  classical
  have h := multiset_threshold_partition t A.charpoly.roots
  change rootCountAbove A.charpoly t + rootCountBelow A.charpoly t +
    A.charpoly.roots.count t = A.charpoly.roots.card at h
  have hc : A.charpoly.roots.card = Fintype.card n := by
    rw [hA.roots_charpoly_eq_eigenvalues, Multiset.card_map]
    rfl
  rw [rootCountAbove_charpoly hA, rootCountBelow_charpoly hA, hc] at h
  exact h

def lastFirstEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm _ _).trans finSumFinEquiv

theorem lastFirstEquiv_inr (n : ℕ) (i : Fin n) :
    lastFirstEquiv n (Sum.inr i) = i.castSucc := rfl

theorem lastFirst_tail_prefix (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (A.submatrix (lastFirstEquiv n) (lastFirstEquiv n)).submatrix Sum.inr Sum.inr =
      A.submatrix Fin.castSucc Fin.castSucc := by
  apply Matrix.ext
  intro i j
  rfl

theorem spectralCountAbove_prefix_upper {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) (t : ℝ) :
    spectralCountAbove hA t ≤ spectralCountAbove (hA.submatrix Fin.castSucc) t + 1 := by
  let hS := hA.submatrix (lastFirstEquiv n)
  let hT := hS.submatrix Sum.inr
  calc
    _ = spectralCountAbove hS t :=
      (spectralCountAbove_submatrix_equiv (lastFirstEquiv n) hA t).symm
    _ ≤ Fintype.card (Fin 1) + spectralCountAbove hT t :=
      spectralCountAbove_le_head_add_tail hS t
    _ = _ := by
      rw [spectralCountAbove_congr hT (hA.submatrix Fin.castSucc) (lastFirst_tail_prefix n A) t]
      simp [Nat.add_comm]

theorem spectralCountBelow_prefix_upper {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) (t : ℝ) :
    spectralCountBelow hA t ≤ spectralCountBelow (hA.submatrix Fin.castSucc) t + 1 := by
  let hS := hA.submatrix (lastFirstEquiv n)
  let hT := hS.submatrix Sum.inr
  calc
    _ = spectralCountBelow hS t :=
      (spectralCountBelow_submatrix_equiv (lastFirstEquiv n) hA t).symm
    _ ≤ Fintype.card (Fin 1) + spectralCountBelow hT t :=
      spectralCountBelow_le_head_add_tail hS t
    _ = _ := by
      rw [spectralCountBelow_congr hT (hA.submatrix Fin.castSucc) (lastFirst_tail_prefix n A) t]
      simp [Nat.add_comm]

theorem principal_root_multiplicity_bounds {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) (t : ℝ) :
    A.charpoly.roots.count t ≤ (A.submatrix Fin.castSucc Fin.castSucc).charpoly.roots.count t + 1 ∧
    (A.submatrix Fin.castSucc Fin.castSucc).charpoly.roots.count t ≤ A.charpoly.roots.count t + 1 := by
  have h1 := spectral_counts_multiplicity hA t
  have h2 := spectral_counts_multiplicity (hA.submatrix Fin.castSucc) t
  have h3 := spectralCountAbove_principal ⟨Fin.castSucc, Fin.castSucc_injective n⟩ hA t
  have h4 := spectralCountBelow_principal ⟨Fin.castSucc, Fin.castSucc_injective n⟩ hA t
  have h5 := spectralCountAbove_prefix_upper hA t
  have h6 := spectralCountBelow_prefix_upper hA t
  simp only [Fintype.card_fin] at h1 h2
  omega

theorem reduced_principal_squarefree {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian)
    (F p q : Polynomial ℝ) (hF : F.Monic) (hp : p.Monic) (hq : q.Monic)
    (hfac0 : (A.submatrix Fin.castSucc Fin.castSucc).charpoly = F * p)
    (hfac1 : A.charpoly = F * q) (hcop : IsCoprime p q) : Squarefree p := by
  classical
  have hsplit : p.Splits := (hA.submatrix Fin.castSucc).splits_charpoly.of_dvd
    (Matrix.charpoly_monic _).ne_zero ⟨F, hfac0.trans (mul_comm F p)⟩
  apply ((Polynomial.nodup_roots_iff_of_splits hp.ne_zero hsplit).mp ?_).squarefree
  apply Multiset.nodup_iff_count_le_one.mpr
  intro t
  by_cases ht : t ∈ p.roots
  · have hpz := (Polynomial.mem_roots hp.ne_zero).mp ht
    change p.eval t = 0 at hpz
    have hqz : q.eval t ≠ 0 := by
      intro hq0
      obtain ⟨u, v, huv⟩ := hcop
      have hh := congrArg (Polynomial.eval t) huv
      simp only [eval_add, eval_mul, eval_one, hpz, hq0, mul_zero, zero_add] at hh
      exact zero_ne_one hh
    have hqc : q.roots.count t = 0 := Multiset.count_eq_zero.mpr
      (fun hm => hqz ((Polynomial.mem_roots hq.ne_zero).mp hm))
    have hm := (principal_root_multiplicity_bounds hA t).2
    rw [hfac0, hfac1, Polynomial.roots_mul (mul_ne_zero hF.ne_zero hp.ne_zero),
      Polynomial.roots_mul (mul_ne_zero hF.ne_zero hq.ne_zero),
      Multiset.count_add, Multiset.count_add, hqc] at hm
    omega
  · simp [Multiset.count_eq_zero.mpr ht]

end KadarYu
