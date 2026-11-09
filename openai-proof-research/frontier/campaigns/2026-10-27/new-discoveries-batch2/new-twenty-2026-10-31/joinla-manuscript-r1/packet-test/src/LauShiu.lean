import AntimagicBasics
import Antimagic
import Mathlib.Tactic.Linarith

namespace LauShiu
abbrev Vertex (r s m : ℕ) := (Fin (2*r*(2*s+1)) × Bool) ⊕ (Fin (2*r) × Fin m)

def Adj (r s m : ℕ) : Vertex r s m → Vertex r s m → Prop
 | .inl (t,b), .inl (u,c) => t = u ∧ b ≠ c
 | .inl (t,_), .inr (h,_) => t.val / (2*s+1) = h.val
 | .inr (h,_), .inl (t,_) => t.val / (2*s+1) = h.val
 | .inr _, .inr _ => False

instance (r s m) : DecidableRel (Adj r s m) := fun v w => by
 cases v <;> cases w <;> simp only [Adj] <;> infer_instance

def graph (r s m : ℕ) : SimpleGraph (Vertex r s m) where
 Adj := Adj r s m
 symm := ⟨by intro v w h; cases v <;> cases w <;> simp_all [Adj, eq_comm]⟩
 loopless := ⟨by intro v; cases v <;> simp [Adj]⟩

instance (r s m) : DecidableRel (graph r s m).Adj := inferInstanceAs (DecidableRel (Adj r s m))

theorem vertex_count (r s m) : Fintype.card (Vertex r s m) = 2*r*(2*(2*s+1)+m) := by
 simp [Vertex, Fintype.card_sum, Fintype.card_prod]; ring

theorem no_isolated (r s m : ℕ) (v : Vertex r s m) : ∃ w, (graph r s m).Adj v w := by
 cases v with
 | inl x => exact ⟨.inl (x.1, !x.2), by cases hb : x.2 <;> simp [graph, Adj, hb]⟩
 | inr x =>
   refine ⟨.inl (⟨x.1.val*(2*s+1), ?_⟩, false), ?_⟩
   · have := x.1.isLt; nlinarith
   · change x.1.val*(2*s+1)/(2*s+1) = x.1.val
     exact Nat.mul_div_cancel _ (by omega)

def vertexMap : R159.V → Vertex 1 1 2
 | .inl x => .inl x
 | .inr (h,b) => .inr (h, if b then 1 else 0)

theorem vertex_bijective : Function.Bijective vertexMap := by decide
noncomputable def vertexEquiv : R159.V ≃ Vertex 1 1 2 := Equiv.ofBijective vertexMap vertex_bijective

theorem adj_correspondence : ∀ v w, (graph 1 1 2).Adj (vertexMap v) (vertexMap w) ↔ R159.sourceAdj v w := by decide

def indexedEdge (e : R159.E) : (graph 1 1 2).edgeSet :=
 ⟨s(vertexMap (R159.ends e).1, vertexMap (R159.ends e).2), by
   rw [SimpleGraph.mem_edgeSet]
   exact (adj_correspondence _ _).mpr ((R159.edge_complete _ _).mpr ⟨e, Or.inl ⟨rfl,rfl⟩⟩)⟩

theorem indexedEdge_injective : Function.Injective indexedEdge := by
 intro e d h
 have he := congrArg Subtype.val h
 have hv : (R159.ends e).1 = (R159.ends d).1 ∧ (R159.ends e).2 = (R159.ends d).2 ∨
     (R159.ends e).1 = (R159.ends d).2 ∧ (R159.ends e).2 = (R159.ends d).1 := by
   simpa only [indexedEdge, Sym2.eq_iff, vertex_bijective.1.eq_iff] using he
 exact R159.edge_unique e d hv

theorem indexedEdge_surjective : Function.Surjective indexedEdge := by
 intro a
 obtain ⟨⟨u,v⟩, huv⟩ := Sym2.mk_surjective a.val
 change s(u,v) = a.val at huv
 obtain ⟨x,rfl⟩ := vertex_bijective.2 u
 obtain ⟨y,rfl⟩ := vertex_bijective.2 v
 have ha : (graph 1 1 2).Adj (vertexMap x) (vertexMap y) := by
   rw [← SimpleGraph.mem_edgeSet]; exact huv.symm ▸ a.property
 obtain ⟨e, he⟩ := (R159.edge_complete x y).mp ((adj_correspondence x y).mp ha)
 refine ⟨e, Subtype.ext ?_⟩
 rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
 · simpa [indexedEdge, h1,h2] using huv
 · simpa [indexedEdge, h1,h2, Sym2.eq_swap] using huv

noncomputable def edgeEquiv : R159.E ≃ (graph 1 1 2).edgeSet :=
 Equiv.ofBijective indexedEdge ⟨indexedEdge_injective, indexedEdge_surjective⟩

theorem instance_edge_count : Fintype.card (graph 1 1 2).edgeSet = 30 := by
 rw [← Fintype.card_congr edgeEquiv]; decide

noncomputable def indexedLabel (f : Antimagic.Labeling (graph 1 1 2)) (e : R159.E) : ℤ :=
 (f (indexedEdge e)).val + 1

theorem indexed_labeling (f : Antimagic.Labeling (graph 1 1 2)) : R159.Labeling (indexedLabel f) := by
 constructor
 · intro e d h
   apply indexedEdge_injective
   apply f.injective
   apply Fin.ext
   dsimp [indexedLabel] at h
   omega
 · intro e
   have := (f (indexedEdge e)).isLt
   have hc := instance_edge_count
   dsimp [indexedLabel]; constructor <;> omega

theorem weight_correspondence (f : Antimagic.Labeling (graph 1 1 2)) (v : R159.V) :
 R159.wt (indexedLabel f) v = (Antimagic.weight (graph 1 1 2) f (vertexMap v) : ℤ) := by
 unfold R159.wt Antimagic.weight
 rw [Nat.cast_sum, ← edgeEquiv.sum_comp]
 apply Finset.sum_congr rfl
 intro e _
 have hm : vertexMap v ∈ (indexedEdge e).val ↔ (R159.ends e).1 = v ∨ (R159.ends e).2 = v := by
   simp [indexedEdge, Sym2.mem_iff, vertex_bijective.1.eq_iff, eq_comm]
 change (if (R159.ends e).1 = v ∨ (R159.ends e).2 = v then indexedLabel f e else 0) = ((if vertexMap v ∈ (indexedEdge e).val then (f (indexedEdge e)).val + 1 else 0 : ℕ) : ℤ)
 simp only [hm]
 split_ifs <;> simp [indexedLabel]

end LauShiu
