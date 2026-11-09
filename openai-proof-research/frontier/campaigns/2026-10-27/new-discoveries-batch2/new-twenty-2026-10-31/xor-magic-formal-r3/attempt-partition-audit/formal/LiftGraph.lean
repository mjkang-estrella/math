import Four
import SeedStructure
namespace XorMagic
variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The transports are specified in both directions, with an inverse law on every edge. -/
structure EdgeTransport (G : SimpleGraph V) where
  map : V → V → Four ≃ Four
  reverse : ∀ {u v}, G.Adj u v → ∀ x, map v u (map u v x) = x

namespace EdgeTransport
variable (T : EdgeTransport G)

def graph : SimpleGraph (V × Four) where
  Adj p q := G.Adj p.1 q.1 ∧ T.map p.1 q.1 p.2 = q.2
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm, h.2 ▸ T.reverse h.1 p.2⟩⟩
  loopless := ⟨by intro p h; exact G.irrefl h.1⟩

instance [DecidableRel G.Adj] : DecidableRel T.graph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def neighborEmbedding (v : V) (x : Four) : V ↪ V × Four where
  toFun u := (u, T.map v u x)
  inj' := by intro a b h; exact congrArg Prod.fst h

theorem neighbors [DecidableRel G.Adj] (v : V) (x : Four) :
    T.graph.neighborFinset (v,x) = (G.neighborFinset v).map (T.neighborEmbedding v x) := by
  ext ⟨u,y⟩
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_map]
  change (G.Adj v u ∧ T.map v u x = y) ↔
    ∃ a, a ∈ G.neighborFinset v ∧ (a,T.map v a x) = (u,y)
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · intro ⟨h,e⟩; exact ⟨u,h,Prod.ext rfl e⟩
  · rintro ⟨a,h,e⟩
    have ha : a = u := congrArg Prod.fst e
    subst a
    exact ⟨h,congrArg Prod.snd e⟩

theorem degree [DecidableRel G.Adj] (p : V × Four) : T.graph.degree p = G.degree p.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, T.neighbors,
    Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]

theorem regular [DecidableRel G.Adj] {d : ℕ} (h : G.IsRegularOfDegree d) :
    T.graph.IsRegularOfDegree d := fun p => (T.degree p).trans (h p.1)

theorem sum_neighbors [DecidableRel G.Adj] {A : Type*} [AddCommMonoid A]
    (f : V × Four → A) (v : V) (x : Four) :
    ∑ p ∈ T.graph.neighborFinset (v,x), f p =
      ∑ u ∈ G.neighborFinset v, f (u,T.map v u x) := by
  rw [T.neighbors, Finset.sum_map]; rfl

theorem sum_first [DecidableRel G.Adj] {n : ℕ} (l : V → Bits n) (v : V) (x : Four) :
    ∑ p ∈ T.graph.neighborFinset (v,x), l p.1 = ∑ u ∈ G.neighborFinset v, l u :=
  T.sum_neighbors _ v x

/-- Each matching of the quotient lifts to a matching, with exact coverage. -/
def matching {d : ℕ} (F : MatchingDecomposition G d) : MatchingDecomposition T.graph d where
  mate i p := (F.mate i p.1, T.map p.1 (F.mate i p.1) p.2)
  involutive i p := by
    have ha : G.Adj p.1 (F.mate i p.1) := (F.cover _ _).mpr ⟨i,rfl⟩
    apply Prod.ext
    · exact F.involutive i p.1
    · simpa only [F.involutive] using T.reverse ha p.2
  no_fixed i p h := F.no_fixed i p.1 (congrArg Prod.fst h)
  distinct p i j h := F.distinct p.1 (congrArg Prod.fst h)
  cover p q := by
    constructor
    · rintro ⟨ha,hx⟩
      obtain ⟨i,hi⟩ := (F.cover _ _).mp ha
      exact ⟨i,Prod.ext hi (by simpa only [hi] using hx)⟩
    · rintro ⟨i,hi⟩
      have hv := congrArg Prod.fst hi
      exact ⟨(F.cover _ _).mpr ⟨i,hv⟩, by simpa only [← hv] using congrArg Prod.snd hi⟩
end EdgeTransport
end XorMagic
