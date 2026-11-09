import StackSortDel5Representation
namespace StackSort.Del5
open Seeds2 Round4

/-- All literal collisions whose common output ends at the maximum. -/
def MaximumPairs (m r s : ℕ) :=
  {p : List (List ℕ) × List (List ℕ) //
    p.1 ∈ tuples (m+1) r ∧ p.2 ∈ tuples (m+1) s ∧
    output p.1 = output p.2 ∧ (output p.1).idxOf m + 1 = m+1}

/-- Reduced prefixes and oriented child suffixes, with the literal arity equations. -/
def ReducedPairs (m r s : ℕ) :=
  {p : (List (List ℕ) × Children) × (List (List ℕ) × Children) //
    p.1.1.length+1 = r ∧ p.2.1.length+1 = s ∧
    p.1.1 ++ childrenTuple p.1.2 ∈ tuples m (p.1.1.length + childrenArity p.1.2) ∧
    p.2.1 ++ childrenTuple p.2.2 ∈ tuples m (p.2.1.length + childrenArity p.2.2) ∧
    output (p.1.1 ++ childrenTuple p.1.2) = output (p.2.1 ++ childrenTuple p.2.2)}

def insertPair {m r s : ℕ} (p : ReducedPairs m r s) : MaximumPairs m r s :=
  ⟨(p.val.1.1 ++ [rootWord m p.val.1.2.parts],
    p.val.2.1 ++ [rootWord m p.val.2.2.parts]), by
    have hA := p.property.2.2.1
    have hB := p.property.2.2.2.1
    obtain ⟨hF,hlast⟩ := representation_maximum_final hA
    have hG := (representation_maximum_final hB).1
    refine ⟨?_,?_,?_,hlast⟩
    · simpa [p.property.1] using hF
    · simpa [p.property.2.1] using hG
    · exact (insert_last_collision hA hB).mpr p.property.2.2.2.2⟩

theorem insertPair_injective (m r s : ℕ) : Function.Injective (@insertPair m r s) := by
  rintro ⟨⟨⟨A,c⟩,⟨B,d⟩⟩,hp⟩ ⟨⟨⟨C,e⟩,⟨D,f⟩⟩,hq⟩ he
  have he' := congrArg Subtype.val he
  have hF := congrArg Prod.fst he'
  have hG := congrArg Prod.snd he'
  obtain ⟨rfl,rfl⟩ := insertion_injective hp.2.2.1 hq.2.2.1 hF
  obtain ⟨rfl,rfl⟩ := insertion_injective hp.2.2.2.1 hq.2.2.2.1 hG
  rfl

theorem insertPair_surjective (m r s : ℕ) : Function.Surjective (@insertPair m r s) := by
  rintro ⟨⟨F,G⟩,hF,hG,he,hlast⟩
  obtain ⟨A,B,c,d,hFc,hGd,hr,hs,hA,hB,hc⟩ :=
    maximum_final_collision_representation hF hG he hlast
  refine ⟨⟨((A,c),(B,d)),hr,hs,hA,hB,hc⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext hFc.symm hGd.symm

/-- The tuple-level deletion bijection on all maximum-final collisions. -/
noncomputable def deletionEquiv (m r s : ℕ) : ReducedPairs m r s ≃ MaximumPairs m r s :=
  Equiv.ofBijective insertPair ⟨insertPair_injective m r s, insertPair_surjective m r s⟩
end StackSort.Del5
