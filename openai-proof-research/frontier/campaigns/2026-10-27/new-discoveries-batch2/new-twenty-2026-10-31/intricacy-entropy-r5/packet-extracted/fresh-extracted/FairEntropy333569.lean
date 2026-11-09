import FairSelections333569

namespace MathDB333569
noncomputable section
open Finset

theorem sum_pairs_by_gap (n : ℕ) (f : ℕ → ℝ) :
    (∑ a : Fin (n+1), ∑ b : Fin (n+1), if a < b then f (b.val-a.val) else 0) =
      ∑ g : Fin n, (n-g.val : ℕ) * f (g.val+1) := by
  classical
  let T : Finset (Fin (n+1) × Fin (n+1)) := univ.filter (fun p => p.1 < p.2)
  have he : (∑ p ∈ T, f (p.2.val-p.1.val)) =
      ∑ q : (Σ g : Fin n, Fin (n-g.val)), f (q.1.val+1) := by
    symm
    apply sum_bij (fun q _ =>
      ((⟨q.2.val,by have := q.2.isLt; omega⟩ : Fin (n+1)),
       (⟨q.2.val+q.1.val+1,by have := q.2.isLt; omega⟩ : Fin (n+1))))
    · intro q _
      apply mem_filter.mpr
      exact ⟨mem_univ _, by change q.2.val < q.2.val+q.1.val+1; omega⟩
    · intro q _ r _ h
      have h₁ := congrArg (fun p : Fin (n+1) × Fin (n+1) => p.1.val) h
      have h₂ := congrArg (fun p : Fin (n+1) × Fin (n+1) => p.2.val) h
      dsimp at h₁ h₂
      have hg : q.1 = r.1 := Fin.ext (by omega)
      cases q with
      | mk g a =>
        cases r with
        | mk j b =>
          dsimp at hg
          subst j
          congr 1
          exact Fin.ext h₁
    · intro p hp
      have hab : p.1.val < p.2.val := (mem_filter.mp hp).2
      let g : Fin n := ⟨p.2.val-p.1.val-1,by have := p.2.isLt; omega⟩
      let a : Fin (n-g.val) := ⟨p.1.val,by dsimp [g]; have := p.2.isLt; omega⟩
      refine ⟨⟨g,a⟩,mem_univ _,?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        dsimp [g,a]
        omega
    · intro q _
      congr 1
      dsimp
      omega
  have hleft : (∑ a : Fin (n+1), ∑ b : Fin (n+1), if a < b then f (b.val-a.val) else 0) =
      ∑ p ∈ T, f (p.2.val-p.1.val) := by
    simp only [T, sum_filter]
    exact (Fintype.sum_prod_type (fun p : Fin (n+1) × Fin (n+1) =>
      if p.1 < p.2 then f (p.2.val-p.1.val) else 0)).symm
  rw [hleft,he,Fintype.sum_sigma]
  apply sum_congr rfl
  intro g _
  simp

/-- Exact fair-subset entropy identity in gap form, N=n+1. -/
theorem fairEntropy_gap_sum {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n : ℕ) :
    (∑ S : Finset (Fin (n+1)), sampleEntropy (chart l t) n S) =
      ((2:ℝ)^(n+1)-1) * initialEntropy (chart l t) +
      ∑ g : Fin n, (n-g.val : ℕ) * (2:ℝ)^(n-g.val-1) * conditionalEntropy (l^(g.val+1)) t := by
  rw [sum_sampleEntropy_pairs hl hl1 ht ht1,
    sum_pairs_by_gap n (fun i => (2:ℝ)^((n+1)-(i+1)) * conditionalEntropy (l^i) t)]
  congr 1
  apply sum_congr rfl
  intro g _
  have hg := g.isLt
  have he : (n+1)-(g.val+1+1) = n-g.val-1 := by omega
  rw [he]
  ring

end
end MathDB333569
