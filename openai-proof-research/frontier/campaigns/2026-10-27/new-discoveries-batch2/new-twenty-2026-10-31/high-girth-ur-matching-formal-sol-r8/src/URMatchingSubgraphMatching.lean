module
public import URMatchingFinite
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
@[expose] public section
namespace URMatching
universe u
variable {V : Type u}

def matchingSubgraph {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hm : IsMatching G M) : G.Subgraph where
  verts := Covered M
  Adj x y := s(x,y) ∈ M
  adj_sub h := hm.1 _ h
  edge_vert h := ⟨_,h,Sym2.mem_mk_left _ _⟩
  symm := ⟨by intro x y h; simpa [Sym2.eq_swap] using h⟩

theorem matchingSubgraph_isMatching {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hm : IsMatching G M) : ∀ ⦃v⦄, v ∈ (matchingSubgraph hm).verts → ∃! w, (matchingSubgraph hm).Adj v w := by
  intro v hv
  obtain ⟨e,he,hve⟩ := hv
  obtain ⟨⟨x,y⟩,rfl⟩ := Sym2.mk_surjective e
  rcases Sym2.mem_iff.mp hve with hv | hv
  · subst v
    refine ⟨y,he,?_⟩
    intro w hw
    have heq := hm.2 s(x,w) hw s(x,y) he x (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
    rcases Sym2.eq_iff.mp heq with ⟨_,hw⟩ | ⟨hx,hw⟩
    · exact hw
    · exact hw.trans hx
  · subst v
    have he' : s(y,x) ∈ M := by simpa [Sym2.eq_swap] using he
    refine ⟨x,he',?_⟩
    intro w hw
    have heq := hm.2 s(y,w) hw s(y,x) he' y (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
    rcases Sym2.eq_iff.mp heq with ⟨_,hw⟩ | ⟨hy,hw⟩
    · exact hw
    · exact hw.trans hy
end URMatching
