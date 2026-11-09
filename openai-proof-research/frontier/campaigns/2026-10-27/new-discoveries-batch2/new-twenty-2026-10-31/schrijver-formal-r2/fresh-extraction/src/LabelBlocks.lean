import IndexedCertificates
set_option autoImplicit false
namespace Schrijver

def labelRangeCheck (N : ℕ) [NeZero N] (masks ds : ℕ → ℕ) (lo count : ℕ) : Bool :=
  (List.range' lo count).all (fun i => (List.finRange N).all (fun v =>
    !indexedEdge masks (Fin.ofNat N i) v ||
      decide (indexDepth ds v ≤ indexDepth ds (Fin.ofNat N i) + 1)))

theorem labelRangeCheck_sound (N : ℕ) [NeZero N] (masks ds : ℕ → ℕ) (lo count : ℕ)
    (h : labelRangeCheck N masks ds lo count = true)
    (u v : Fin N) (hu : lo ≤ u.val ∧ u.val < lo + count)
    (he : (indexedGraph N masks).Adj u v) : indexDepth ds v ≤ indexDepth ds u + 1 := by
  have hh := (List.all_eq_true.mp h) u.val (List.mem_range'.mpr ⟨u.val-lo, by omega, by omega⟩)
  have hv := (List.all_eq_true.mp hh) v (by simp)
  have hi : Fin.ofNat N u.val = u := by simp
  rw [hi, (indexedEdge_iff _ _ _).mpr he] at hv
  simpa using hv

end Schrijver
