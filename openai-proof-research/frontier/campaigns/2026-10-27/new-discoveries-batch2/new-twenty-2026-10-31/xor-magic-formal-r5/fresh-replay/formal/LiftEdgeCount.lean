import LiftIncidence
import TranslationCardinality
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

def dartOrientation : G.Dart ≃ OrientedEdge G × Bool where
  toFun d := if h : d.fst < d.snd then (⟨d.toProd,h,d.adj⟩,true)
    else (⟨(d.snd,d.fst),lt_of_le_of_ne (le_of_not_gt h) d.snd_ne_fst,d.adj.symm⟩,false)
  invFun p := if p.2 then ⟨p.1.val,p.1.property.2⟩
    else ⟨(p.1.val.2,p.1.val.1),p.1.property.2.symm⟩
  left_inv d := by
    by_cases h : d.fst < d.snd <;> simp only [h, dite_true, dite_false, Bool.false_eq_true,
      ↓reduceIte]
  right_inv p := by
    rcases p with ⟨e,b⟩
    cases b
    · have h : ¬ e.val.2 < e.val.1 := not_lt_of_gt e.property.1
      simp only [Bool.false_eq_true, ↓reduceIte, h, dite_false]
    · simp only [↓reduceIte, e.property.1, dite_true]

theorem oriented_edge_count {d : ℕ} (reg : G.IsRegularOfDegree d) :
    2 * Fintype.card (OrientedEdge G) = d*m := by
  have h := Fintype.card_congr (dartOrientation G)
  rw [G.dart_card_eq_sum_degrees] at h
  have hs : (∑ v : Fin m, G.degree v) = m*d := by
    calc
      _ = ∑ _ : Fin m, d := Finset.sum_congr rfl (fun v _ => reg v)
      _ = m*d := by simp
  rw [hs] at h
  simp only [Fintype.card_prod, Fintype.card_bool] at h
  nlinarith


theorem oriented_edge_count_div {d : ℕ} (reg : G.IsRegularOfDegree d) :
    Fintype.card (OrientedEdge G) = d*m/2 := by
  have h := oriented_edge_count G reg
  omega

theorem affine_translation_exists {d : ℕ} (reg : G.IsRegularOfDegree d) (hd : 4 ≤ d)
    (s : OrientedEdge G → Fin 3) (e : OrientedEdge G) :
    ∃ c : OrientedEdge G → Four, incidenceB G s c = 0 ∧ c ∉ (incidenceD G s).range := by
  apply translation_exists (incidenceD G s) (incidenceB G s) ?_ (incidenceBD_nonzero G s e)
  have hc := oriented_edge_count G reg
  have he : m+m ≤ Fintype.card (OrientedEdge G) := by nlinarith
  have fourcard : Fintype.card Four = 4 := by decide
  simp only [Fintype.card_fun, Fintype.card_fin, fourcard, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) he
end XorMagic
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
theorem affine_translation_exists_regular [Nonempty (Fin m)] {d : ℕ}
    (reg : G.IsRegularOfDegree d) (hd : 4 ≤ d) (s : OrientedEdge G → Fin 3) :
    ∃ c : OrientedEdge G → Four, incidenceB G s c = 0 ∧ c ∉ (incidenceD G s).range := by
  classical
  let u : Fin m := Classical.choice inferInstance
  have hc : 0 < (G.neighborFinset u).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, reg u]
    omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hc
  have ha : G.Adj u v := by simpa using hv
  rcases lt_or_gt_of_ne ha.ne with h | h
  · exact affine_translation_exists G reg hd s ⟨(u,v),h,ha⟩
  · exact affine_translation_exists G reg hd s ⟨(v,u),h,ha.symm⟩
end XorMagic
