import StackSortInj2Fixed
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

noncomputable section
namespace StackSort.Shuffle3
/-- Extend the increasing enumeration of a finite label set to all naturals.
The tail lies strictly above every label. -/
def labelFun (A : Finset ℕ) (x : ℕ) : ℕ :=
  if h : x < A.card then A.orderEmbOfFin rfl ⟨x,h⟩ else A.sup id + 1 + (x-A.card)

theorem labelFun_strictMono (A : Finset ℕ) : StrictMono (labelFun A) := by
  intro x y hxy
  unfold labelFun
  split_ifs with hx hy hy
  · exact (A.orderEmbOfFin rfl).strictMono (show (⟨x,hx⟩ : Fin A.card) < ⟨y,hy⟩ from hxy)
  · have hb : A.orderEmbOfFin rfl ⟨x,hx⟩ ≤ A.sup id :=
      Finset.le_sup (f := id) (A.orderEmbOfFin_mem rfl ⟨x,hx⟩)
    omega
  · omega
  · omega

def labels (A : Finset ℕ) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (labelFun A) (labelFun_strictMono A)

theorem labels_range (A : Finset ℕ) : (List.range A.card).map (labels A) = A.sort := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < A.card := by simpa using hi
    simp [labels, labelFun, h, Finset.orderEmbOfFin_apply]

/-- Literal words with precisely the finite set of labels A. -/
def labelWords (A : Finset ℕ) : Finset (List ℕ) := A.sort.permutations'.toFinset

theorem labelWords_eq_image (A : Finset ℕ) :
    labelWords A = (words A.card).image (List.map (labels A)) := by
  rw [labelWords, words, ← labels_range, ← List.map_permutations']
  ext w
  simp

theorem mem_labelWords {A : Finset ℕ} {w : List ℕ} :
    w ∈ labelWords A ↔ w.Perm A.sort := by simp [labelWords, List.mem_permutations']

/-- Standardisation is a bijection, and equal sorted outputs are reflected as well as preserved. -/
theorem labels_collision_iff (A : Finset ℕ) (u v : List ℕ) :
    s (u.map (labels A)) = s (v.map (labels A)) ↔ s u = s v := by
  rw [s_map_orderEmbedding, s_map_orderEmbedding]
  exact List.map_inj_right (labels A).injective

def labelPairs (A : Finset ℕ) : Finset (List ℕ × List ℕ) :=
  (labelWords A ×ˢ labelWords A).filter (fun p => s p.1 = s p.2)

theorem labelPairs_card (A : Finset ℕ) : (labelPairs A).card = P A.card := by
  let f := fun p : List ℕ × List ℕ => (p.1.map (labels A), p.2.map (labels A))
  have he : labelPairs A =
      (((words A.card ×ˢ words A.card).filter (fun p => s p.1 = s p.2)).image f) := by
    ext p
    simp only [labelPairs, labelWords_eq_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_image]
    rcases p with ⟨p₁,p₂⟩
    constructor
    · rintro ⟨⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,hs⟩
      exact ⟨(u,v), ⟨⟨hu,hv⟩,(labels_collision_iff A u v).mp hs⟩,rfl⟩
    · rintro ⟨⟨u,v⟩,⟨⟨hu,hv⟩,hs⟩,he⟩
      change (u.map (labels A),v.map (labels A)) = (p₁,p₂) at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact ⟨⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,(labels_collision_iff A u v).mpr hs⟩
  rw [he, Finset.card_image_of_injective]
  · rfl
  · intro p q h
    exact Prod.ext ((List.map_inj_right (labels A).injective).mp (congrArg Prod.fst h))
      ((List.map_inj_right (labels A).injective).mp (congrArg Prod.snd h))
end StackSort.Shuffle3
