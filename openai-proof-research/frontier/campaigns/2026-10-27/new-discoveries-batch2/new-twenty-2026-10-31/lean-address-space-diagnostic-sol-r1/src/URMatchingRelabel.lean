module
public import URMatchingFinite
@[expose] public section
namespace URMatching
universe u v
variable {V : Type u} {W : Type v}
noncomputable def mappedEdges (f : V → W) (M : Finset (Sym2 V)) : Finset (Sym2 W) := by
  classical
  exact M.image (Sym2.map f)

theorem mapped_matching {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
    (hf : Function.Injective f) (hg : ∀ x y, G.Adj x y → H.Adj (f x) (f y))
    {M : Finset (Sym2 V)} (hm : IsMatching G M) : IsMatching H (mappedEdges f M) := by
  classical
  constructor
  · intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have hea := hm.1 a ha
    revert hea
    refine Sym2.inductionOn a ?_
    intro x y hxy
    exact hg x y hxy
  · intro e he d hd w hwe hwd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨x,hx,hfx⟩ := Sym2.mem_map.mp hwe
    obtain ⟨y,hy,hfy⟩ := Sym2.mem_map.mp hwd
    have hxy := hf (hfx.trans hfy.symm)
    have hab := hm.2 a ha b hb x hx (hxy ▸ hy)
    exact congrArg (Sym2.map f) hab

theorem mappedEdges_inverse (e : V ≃ W) (M : Finset (Sym2 V)) :
    mappedEdges e.symm (mappedEdges e M) = M := by
  classical
  have hi (a : Sym2 V) : Sym2.map e.symm (Sym2.map e a) = a := by
    refine Sym2.inductionOn a ?_
    intro x y
    simp
  simp only [mappedEdges, Finset.image_image, Function.comp_def, hi]
  ext x
  simp

theorem mappedEdges_injective (e : V ≃ W) : Function.Injective (Sym2.map e) := by
  intro a b he
  have hi (a : Sym2 V) : Sym2.map e.symm (Sym2.map e a) = a := by
    refine Sym2.inductionOn a ?_
    intro x y
    simp
  simpa only [hi] using congrArg (Sym2.map e.symm) he

theorem mappedEdges_card (e : V ≃ W) (M : Finset (Sym2 V)) :
    (mappedEdges e M).card = M.card := by
  classical
  exact Finset.card_image_of_injective _ (mappedEdges_injective e)

theorem mapped_covered (f : V → W) (M : Finset (Sym2 V)) :
    Covered (mappedEdges f M) = f '' Covered M := by
  classical
  ext w
  constructor
  · rintro ⟨d,hd,hw⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨x,hx,hfx⟩ := Sym2.mem_map.mp hw
    exact ⟨x,⟨a,ha,hx⟩,hfx⟩
  · rintro ⟨x,⟨a,ha,hx⟩,rfl⟩
    exact ⟨Sym2.map f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,Sym2.mem_map.mpr ⟨x,hx,rfl⟩⟩

theorem mapped_ur {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hg : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
    {M : Finset (Sym2 V)} (hm : IsUR G M) : IsUR H (mappedEdges e M) := by
  classical
  refine ⟨mapped_matching e e.injective (fun x y h => (hg x y).mp h) hm.1,?_⟩
  intro Q hq hc
  have hback : IsMatching G (mappedEdges e.symm Q) :=
    mapped_matching e.symm e.symm.injective
      (fun x y h => (hg (e.symm x) (e.symm y)).mpr (by simpa using h)) hq
  have hcov : Covered (mappedEdges e.symm Q) = Covered M := by
    rw [mapped_covered,hc,mapped_covered]
    ext x
    simp
  have heq := hm.2 _ hback hcov
  have hh := congrArg (mappedEdges e) heq
  have hqi : mappedEdges e (mappedEdges e.symm Q) = Q := by
    simpa only [Equiv.symm_symm] using mappedEdges_inverse e.symm Q
  exact hqi.symm.trans hh
end URMatching
