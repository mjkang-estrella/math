import StackSortShuffle3Core
import StackSortSeeds2Final
noncomputable section
open BigOperators
namespace StackSort.Shuffle3
open Seeds2

def tupleMap (φ : ℕ ↪o ℕ) (F : List (List ℕ)) := F.map (List.map φ)
 theorem tupleMap_injective (φ : ℕ ↪o ℕ) : Function.Injective (tupleMap φ) :=
  fun _ _ h => (List.map_inj_right (fun _ _ he => (List.map_inj_right φ.injective).mp he)).mp h
 theorem output_tupleMap (φ : ℕ ↪o ℕ) (F : List (List ℕ)) :
    output (tupleMap φ F) = (output F).map φ := by
  induction F with
  | nil => rfl
  | cons w F ih => simpa [tupleMap,output,s_map_orderEmbedding,List.map_append] using ih
 theorem tuple_collision_iff (φ : ℕ ↪o ℕ) (F G : List (List ℕ)) :
    output (tupleMap φ F) = output (tupleMap φ G) ↔ output F = output G := by
  rw [output_tupleMap,output_tupleMap]
  exact List.map_inj_right φ.injective

/-- A general pattern family: a chosen tuple-pair family can encode any prescribed cuts
or irreducibility. Relabelling is an actual bijection onto its image. -/
def tupleFamily (A : Finset ℕ) (F : Finset (List (List ℕ) × List (List ℕ))) :=
  F.image (fun p => (tupleMap (labels A) p.1, tupleMap (labels A) p.2))
 theorem tupleFamily_card (A : Finset ℕ) (F : Finset (List (List ℕ) × List (List ℕ))) :
    (tupleFamily A F).card = F.card := by
  apply Finset.card_image_of_injective
  intro p q h
  exact Prod.ext (tupleMap_injective _ (congrArg Prod.fst h))
    (tupleMap_injective _ (congrArg Prod.snd h))

/-- General labelled-subset tensor count, with arbitrary standardized pattern families.
Both ordinary collisions and irreducible blocks can be supplied as F and G. -/
def tupleShuffle (n i : ℕ)
    (F G : Finset (List (List ℕ) × List (List ℕ))) :=
  ((Finset.range n).powersetCard i).sigma
    (fun A => tupleFamily A F ×ˢ tupleFamily (Finset.range n \ A) G)
 theorem tupleShuffle_card (n i : ℕ)
    (F G : Finset (List (List ℕ) × List (List ℕ))) :
    (tupleShuffle n i F G).card = Nat.choose n i * F.card * G.card := by
  simp only [tupleShuffle,Finset.card_sigma,Finset.card_product,tupleFamily_card,
    Finset.sum_const,Finset.card_powersetCard,Finset.card_range,smul_eq_mul]
  exact (Nat.mul_assoc _ _ _).symm

/-- A tuple pair relabelled by the common increasing map remains a collision. -/
 theorem tupleFamily_collision (A : Finset ℕ)
    (F : Finset (List (List ℕ) × List (List ℕ)))
    (hF : ∀ p ∈ F, output p.1 = output p.2) :
    ∀ p ∈ tupleFamily A F, output p.1 = output p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact (tuple_collision_iff _ _ _).mpr (hF q hq)
 theorem boundary_tupleMap_iff (φ : ℕ ↪o ℕ) (F : List (List ℕ)) (k : ℕ) :
    Boundary (tupleMap φ F) k ↔ Boundary F k := by
  constructor
  · rintro ⟨A,B,he,hk⟩
    obtain ⟨U,V,hF,hU,_⟩ := List.map_eq_append_iff.mp he
    refine ⟨U,V,hF,?_⟩
    change tupleMap φ U = A at hU
    rw [← hU,output_tupleMap,List.length_map] at hk
    exact hk
  · rintro ⟨A,B,rfl,hk⟩
    refine ⟨tupleMap φ A,tupleMap φ B,by simp [tupleMap],?_⟩
    simpa only [output_tupleMap,List.length_map] using hk

 theorem irreducible_tupleMap_iff (φ : ℕ ↪o ℕ) (F G : List (List ℕ)) :
    Irreducible (tupleMap φ F) (tupleMap φ G) ↔ Irreducible F G := by
  simp only [Seeds2.Irreducible,boundary_tupleMap_iff,output_tupleMap,List.length_map]

 def fixedTupleShuffle (n i : ℕ) (S : Finset ℕ)
    (F G : Finset (List (List ℕ) × List (List ℕ))) :=
  (((Finset.range n).powersetCard i).filter (S ⊆ ·)).sigma
    (fun A => tupleFamily A F ×ˢ tupleFamily (Finset.range n \ A) G)
 theorem fixedTupleShuffle_card (n i : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) (hi : S.card ≤ i)
    (F G : Finset (List (List ℕ) × List (List ℕ))) :
    (fixedTupleShuffle n i S F G).card =
      Nat.choose (n-S.card) (i-S.card) * F.card * G.card := by
  simp only [fixedTupleShuffle,Finset.card_sigma,Finset.card_product,tupleFamily_card,
    Finset.sum_const,smul_eq_mul]
  rw [Finset.card_filter_powersetCard_subset S (Finset.range n) i hS hi,Finset.card_range]
  exact (Nat.mul_assoc _ _ _).symm
end StackSort.Shuffle3
