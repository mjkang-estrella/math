import Encoding
namespace Schrijver
set_option autoImplicit false

-- Subtracting rank turns gaps of at least two into strict increases.
def subtractRank (a : ℕ → ℕ) (i : ℕ) : ℕ := a i - i

theorem gap_chain {a : ℕ → ℕ} {k : ℕ}
    (hg : ∀ i, i+1 < k → a i + 2 ≤ a (i+1)) :
    ∀ j, j < k → ∀ i, i ≤ j → a i + 2*(j-i) ≤ a j := by
  intro j
  induction j with
  | zero =>
    intro _hj i hi
    have he : i = 0 := by omega
    subst i
    omega
  | succ j ih =>
    intro hj i hi
    by_cases he : i = j+1
    · subst i; omega
    · have hh := ih (by omega) i (by omega)
      have hs := hg j hj
      omega

theorem rank_le_of_gaps {a : ℕ → ℕ} {k i : ℕ}
    (hg : ∀ j, j+1 < k → a j + 2 ≤ a (j+1)) (hi : i < k) :
    i ≤ a i := by
  have h := gap_chain hg i hi 0 (by omega)
  omega

theorem subtractRank_inverse {a : ℕ → ℕ} {k i : ℕ}
    (hg : ∀ j, j+1 < k → a j + 2 ≤ a (j+1)) (hi : i < k) :
    subtractRank a i + i = a i := by
  exact Nat.sub_add_cancel (rank_le_of_gaps hg hi)

theorem subtractRank_strict {a : ℕ → ℕ} {k i j : ℕ}
    (hg : ∀ l, l+1 < k → a l + 2 ≤ a (l+1))
    (hij : i < j) (hj : j < k) : subtractRank a i < subtractRank a j := by
  have hc := gap_chain hg j hj i (by omega)
  have hi := rank_le_of_gaps hg (show i < k by omega)
  have hj' := rank_le_of_gaps hg hj
  unfold subtractRank
  omega

theorem subtractRank_bound {a : ℕ → ℕ} {n k i : ℕ}
    (hg : ∀ j, j+1 < k → a j + 2 ≤ a (j+1))
    (hb : ∀ j, j < k → a j < n) (hi : i < k) :
    subtractRank a i < n-k+1 := by
  have hk : k-1 < k := by omega
  have hc := gap_chain hg (k-1) hk i (by omega)
  have hl := hb (k-1) hk
  have hr := rank_le_of_gaps hg hi
  unfold subtractRank
  omega
end Schrijver
