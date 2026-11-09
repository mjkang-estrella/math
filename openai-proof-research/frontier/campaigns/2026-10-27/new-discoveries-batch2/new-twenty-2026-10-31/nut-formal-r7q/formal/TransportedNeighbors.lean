import GraphDeletion
import ExtensionEncoding
namespace Nut8
/-- Extend an old labelling to send the new final vertex to the deleted vertex. -/
def extendLabels {n : ℕ} (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr e).trans (finSuccEquiv' v).symm)

lemma extendLabels_last {n : ℕ} (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) :
    extendLabels v e (Fin.last n) = v := by
  simp [extendLabels]

lemma extendLabels_castSucc {n : ℕ} (v : Fin (n+1)) (e : Equiv.Perm (Fin n))
    (i : Fin n) : extendLabels v e i.castSucc = v.succAbove (e i) := by
  simp [extendLabels, finSuccEquiv'_symm_some]

attribute [local instance] Classical.propDecidable
/-- The transported neighbourhood, encoded in exactly n binary places. -/
noncomputable def transportedMask {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) : ℕ :=
  encodeBits n (fun k => if hk : k < n then decide (G.Adj v (v.succAbove (e ⟨k,hk⟩))) else false)

theorem transportedMask_lt {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) : transportedMask G v e < 2^n :=
  encodeBits_lt _ _

theorem transportedMask_bit {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (transportedMask G v e).testBit i.val = true ↔ G.Adj v (v.succAbove (e i)) := by
  simp [transportedMask, encodeBits_testBit, i.isLt]
/-- The full transported graph, including the new vertex, has the encoded extension bits. -/
theorem transported_extension_spec {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) (a : ℕ)
    (ha : ∀ i j : Fin n, G.Adj (v.succAbove (e i)) (v.succAbove (e j)) ↔
      graphBit n a i.val j.val = true) (i j : Fin (n+1)) :
    G.Adj (extendLabels v e i) (extendLabels v e j) ↔
      graphBit (n+1) (extendGraph n a (transportedMask G v e)) i.val j.val = true := by
  rw [extendGraph_testBit _ _ _ _ _ i.isLt j.isLt]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [extensionBit, extendLabels_last]
  · simpa [extensionBit, extendLabels_last, extendLabels_castSucc,
      Nat.ne_of_lt j.isLt] using (transportedMask_bit G v e j).symm
  · simpa [extensionBit, extendLabels_last, extendLabels_castSucc,
      Nat.ne_of_lt i.isLt, G.adj_comm] using (transportedMask_bit G v e i).symm
  · simpa [extensionBit, extendLabels_castSucc, Nat.ne_of_lt i.isLt,
      Nat.ne_of_lt j.isLt] using ha i j
end Nut8
