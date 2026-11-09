import LauShiu
namespace LauShiu
abbrev EdgeIndex (r s m : ℕ) := Fin (2*r*(2*s+1)) × Option (Bool × Fin m)
def component {r s : ℕ} (t : Fin (2*r*(2*s+1))) : Fin (2*r) :=
 ⟨t.val/(2*s+1), (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using t.isLt)⟩
def generalEnds {r s m : ℕ} (e : EdgeIndex r s m) : Vertex r s m × Vertex r s m :=
 match e.2 with
 | none => (.inl (e.1,false), .inl (e.1,true))
 | some (b,j) => (.inl (e.1,b), .inr (component e.1,j))
def generalEdge {r s m : ℕ} (e : EdgeIndex r s m) : (graph r s m).edgeSet :=
 ⟨s((generalEnds e).1,(generalEnds e).2), by
   rw [SimpleGraph.mem_edgeSet]
   rcases e with ⟨t, _ | ⟨b,j⟩⟩ <;> simp [generalEnds, graph, Adj, component]⟩

theorem generalEdge_injective (r s m : ℕ) : Function.Injective (@generalEdge r s m) := by
 rintro ⟨t, a⟩ ⟨u, c⟩ h
 have he := congrArg Subtype.val h
 cases a with
 | none => cases c <;> simp_all [generalEdge, generalEnds]
 | some a => cases c <;> simp_all [generalEdge, generalEnds, Prod.ext_iff]

theorem generalEdge_surjective (r s m : ℕ) : Function.Surjective (@generalEdge r s m) := by
 intro a
 obtain ⟨⟨v,w⟩, he⟩ := Sym2.mk_surjective a.val
 change s(v,w) = a.val at he
 have ha : (graph r s m).Adj v w := by
   rw [← SimpleGraph.mem_edgeSet]; exact he.symm ▸ a.property
 suffices ∃ e : EdgeIndex r s m, s((generalEnds e).1,(generalEnds e).2) = s(v,w) by
   obtain ⟨e,hh⟩ := this
   exact ⟨e, Subtype.ext (hh.trans he)⟩
 clear he a
 cases v with
 | inl x =>
   cases w with
   | inl y =>
     obtain ⟨t,b⟩ := x; obtain ⟨u,c⟩ := y
     change t=u ∧ b≠c at ha
     obtain ⟨rfl,hbc⟩ := ha
     refine ⟨(t,none), ?_⟩
     cases b <;> cases c <;> simp_all [generalEnds]
   | inr y =>
     obtain ⟨t,b⟩ := x; obtain ⟨h,j⟩ := y
     have hh : component t = h := Fin.ext ha
     exact ⟨(t,some (b,j)), by simp [generalEnds, hh]⟩
 | inr x =>
   cases w with
   | inl y =>
     obtain ⟨h,j⟩ := x; obtain ⟨t,b⟩ := y
     have hh : component t = h := Fin.ext ha
     exact ⟨(t,some (b,j)), by simp [generalEnds, hh]⟩
   | inr y => exact False.elim ha

noncomputable def generalEdgeEquiv (r s m : ℕ) : EdgeIndex r s m ≃ (graph r s m).edgeSet :=
 Equiv.ofBijective generalEdge ⟨generalEdge_injective r s m, generalEdge_surjective r s m⟩

theorem edge_count (r s m : ℕ) :
 Fintype.card (graph r s m).edgeSet = 2*r*((2*s+1)+2*(2*s+1)*m) := by
 rw [← Fintype.card_congr (generalEdgeEquiv r s m)]
 simp [EdgeIndex, Fintype.card_prod]; ring
end LauShiu
