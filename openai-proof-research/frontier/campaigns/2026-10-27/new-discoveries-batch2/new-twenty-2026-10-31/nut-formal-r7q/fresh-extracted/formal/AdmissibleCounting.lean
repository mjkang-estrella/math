import CubicCancellation
import MatrixExtraction
import NutConnected
namespace Nut8
open Matrix
variable {m : ℕ} [NeZero m]

/-- The actual number of neighbors in a fixed orbit, before character weighting. -/
def orbitNeighbors (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]
    (i j : Fin 8) : Finset (ZMod m) :=
  Finset.univ.filter (fun b => G.Adj (i,0) (j,b))

lemma mem_orbitNeighbors (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]
    (i j : Fin 8) (b : ZMod m) : b ∈ orbitNeighbors G i j ↔ G.Adj (i,0) (j,b) := by
  simp [orbitNeighbors]

/-- Coherence removes cancellation in the very same signed quotient entry. -/
theorem abs_signedQuotient_eq_card
    (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj] (hc : Cubic G)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0))
    (i j : Fin 8) : |signedQuotient m G ε i j| = (orbitNeighbors G i j).card := by
  have hs : signedQuotient m G ε i j =
      ∑ b ∈ orbitNeighbors G i j, character m ε b := by
    simp [signedQuotient, orbitNeighbors, Finset.sum_filter]
  rw [hs]
  by_cases hn : (orbitNeighbors G i j).Nonempty
  · obtain ⟨b, hb⟩ := hn
    have hh : ∀ c ∈ orbitNeighbors G i j, character m ε c = character m ε b := by
      intro c hc'
      exact neighbor_character_coherent G hc ε he u hu hf hchar i j c b
        ((mem_orbitNeighbors G i j c).mp hc') ((mem_orbitNeighbors G i j b).mp hb)
    rw [Finset.sum_congr rfl hh, Finset.sum_const, nsmul_eq_mul, abs_mul]
    rcases character_sign m ε he b with h | h <;> simp [h]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

theorem signedQuotient_nonneg (G : SimpleGraph (Fin 8 × ZMod m))
    [DecidableRel G.Adj] (i j : Fin 8) : 0 ≤ signedQuotient m G 1 i j := by
  apply Finset.sum_nonneg
  intro b _
  simp only [character, one_pow]
  split_ifs <;> norm_num

/-- A genuine graph cut yields a nonzero crossing entry, because coherence prevents
the signed sum from erasing that edge. -/
theorem signedQuotient_supportConnected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G)
    (L : Fin 8 × ZMod m ≃ V) (ht : TranslationInvariant (coordinateGraph G L))
    (ε : ℤ) (he : ε = 1 ∨ ε = -1)
    (hc : Cubic (coordinateGraph G L))
    (u : (Fin 8 × ZMod m) → ℝ) (hu : adjacency (coordinateGraph G L) u = 0)
    (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0)) :
    SupportConnected (signedQuotient m (coordinateGraph G L) ε) := by
  classical
  intro S hs hproper
  obtain ⟨i, hi⟩ := hs
  have hex : ∃ j, j ∉ S := by
    by_contra hh
    apply hproper
    apply Finset.eq_univ_of_forall
    simpa only [not_exists, not_not] using hh
  obtain ⟨j, hj⟩ := hex
  obtain ⟨x, hx, y, hy, hxy⟩ := nut_crossing G hn
    {v | (L.symm v).1 ∈ S} (L (i,0)) (L (j,0)) (by simpa) (by simpa)
  let p := L.symm x
  let q := L.symm y
  have hedge : (coordinateGraph G L).Adj (p.1,0) (q.1,q.2-p.2) := by
    apply (ht p.1 q.1 p.2 q.2).mp
    change G.Adj (L (L.symm x)) (L (L.symm y))
    simpa using hxy
  refine ⟨p.1, hx, q.1, hy, ?_⟩
  intro hz
  have hcard := abs_signedQuotient_eq_card (coordinateGraph G L) hc ε he u hu hf hchar p.1 q.1
  rw [hz, abs_zero] at hcard
  have hne : (orbitNeighbors (coordinateGraph G L) p.1 q.1).Nonempty :=
    ⟨q.2-p.2, (mem_orbitNeighbors _ _ _ _).mpr hedge⟩
  have hpos := Finset.card_pos.mpr hne
  exact (ne_of_gt hpos) (by exact_mod_cast hcard.symm)

/-- Cubic degree is preserved by the actual coordinate equivalence. -/
theorem coordinateGraph_cubic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : Fin 8 × ZMod m ≃ V)
    (hc : Cubic G) : Cubic (coordinateGraph G L) := by
  intro p
  change ((coordinateGraph G L).neighborFinset p).card = 3
  rw [Finset.card_equiv L (s := (coordinateGraph G L).neighborFinset p)
    (t := G.neighborFinset (L p)) (by intro q; simp only [SimpleGraph.mem_neighborFinset]; rfl)]
  exact hc (L p)

/-- The orbit fibers partition the actual neighbor set, with no weighting. -/
theorem orbitNeighbors_row (G : SimpleGraph (Fin 8 × ZMod m))
    [DecidableRel G.Adj] (i : Fin 8) :
    (∑ j, ((orbitNeighbors G i j).card : ℤ)) = G.degree (i,0) := by
  have hh : ∀ j, ((orbitNeighbors G i j).card : ℤ) =
      ∑ b : ZMod m, if G.Adj (i,0) (j,b) then (1 : ℤ) else 0 := by
    intro j
    simp [orbitNeighbors]
  simp_rw [hh]
  change (∑ j, ∑ b, (fun p : Fin 8 × ZMod m => if G.Adj (i,0) p then (1 : ℤ) else 0) (j,b)) = _
  rw [← Fintype.sum_prod_type (fun p : Fin 8 × ZMod m => if G.Adj (i,0) p then (1 : ℤ) else 0)]
  simp only [Finset.sum_boole]
  rw [← SimpleGraph.neighborFinset_eq_filter]
  rfl

theorem signedQuotient_abs_row (G : SimpleGraph (Fin 8 × ZMod m))
    [DecidableRel G.Adj] (hc : Cubic G)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0))
    (i : Fin 8) : ∑ j, |signedQuotient m G ε i j| = 3 := by
  simp_rw [abs_signedQuotient_eq_card G hc ε he u hu hf hchar]
  rw [orbitNeighbors_row, hc]
  norm_num

/-- A cubic symmetric connected support on eight vertices cannot have a triple entry:
that entry would saturate both endpoint rows and isolate at most two vertices. -/
theorem connected_cubic_entry_bound (C : QuotientMatrix)
    (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, |C i j| = 3)
    (hc : SupportConnected C) : ∀ i j, |C i j| ≤ 2 := by
  classical
  have hle (i j : Fin 8) : |C i j| ≤ 3 := by
    rw [← hr i]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (C i k)) (Finset.mem_univ j)
  have hzero (i j : Fin 8) (hij : |C i j| = 3) (k : Fin 8) (hkj : k ≠ j) :
      C i k = 0 := by
    have hsum := Finset.sum_erase_add Finset.univ (fun b => |C i b|) (Finset.mem_univ j)
    have hz : ∑ b ∈ Finset.univ.erase j, |C i b| = 0 := by rw [hr, hij] at hsum; omega
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => abs_nonneg (C i b))).mp hz
    exact abs_eq_zero.mp (hterm k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩))
  intro i j
  by_contra hbad
  have hij : |C i j| = 3 := by have := hle i j; omega
  have hji : |C j i| = 3 := by rw [hs j i]; exact hij
  let S : Finset (Fin 8) := {i,j}
  have hproper : S ≠ Finset.univ := by
    intro heq
    have hcard : S.card ≤ 2 := Finset.card_insert_le _ _
    rw [heq] at hcard
    norm_num at hcard
  obtain ⟨x, hx, y, hy, hxy⟩ := hc S (by simp [S]) hproper
  have hyi : y ≠ i := by intro h; apply hy; simp [S, h]
  have hyj : y ≠ j := by intro h; apply hy; simp [S, h]
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · subst x; exact hxy (hzero i j hij y hyj)
  · subst x; exact hxy (hzero j i hji y hyi)

/-- Pointwise equality of the frozen unsignedQuotient with actual neighbor counts. -/
theorem unsignedQuotient_actual (G : SimpleGraph (Fin 8 × ZMod m))
    [DecidableRel G.Adj] (hc : Cubic G)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0)) :
    unsignedQuotient (signedQuotient m G ε) =
      fun i j => ((orbitNeighbors G i j).card : ℤ) := by
  funext i j
  exact abs_signedQuotient_eq_card G hc ε he u hu hf hchar i j
end Nut8



