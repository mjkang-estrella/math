import StackSortCut5Final
import StackSortDel5Final
noncomputable section
namespace StackSort.Fixed6
open Seeds2 Round4 Cut5 Del5 Classical BigOperators

def lastMax (M : ℕ) (p : Cut5.Pair) : Prop := (output p.1).idxOf (M-1)+1=M

theorem labelled_max_last {M a c : ℕ} {A : Finset ℕ} {B D : Cut5.Tuple}
    (hB : B ∈ labelledTuples A a) (hD : D ∈ labelledTuples A c)
    (hsub : A ⊆ Finset.range M) (hm : M-1 ∈ A)
    (he : output B = output D) (hi : Irreducible B D) :
    (output B).idxOf (M-1)+1 = (output B).length := by
  have hb : ∀ x ∈ B.flatten, x ≤ M-1 := by
    intro x hx
    have hxA : x ∈ A := by rw [← support_eq hB]; simpa [support] using hx
    have := Finset.mem_range.mp (hsub hxA); omega
  have hd : ∀ x ∈ D.flatten, x ≤ M-1 := by
    intro x hx
    have hxA : x ∈ A := by rw [← support_eq hD]; simpa [support] using hx
    have := Finset.mem_range.mp (hsub hxA); omega
  apply irreducible_maximum_last B D (M-1) (labelled_nodup hB) (labelled_nodup hD)
    _ _ hb hd he hi
  · have : M-1 ∈ support B := by rw [support_eq hB]; exact hm
    simpa [support] using this
  · have : M-1 ∈ support D := by rw [support_eq hD]; exact hm
    simpa [support] using this

theorem glue_last_iff {M r s : ℕ} {p : Sigma (fun _ : Index => Cut5.Pair × Cut5.Pair)}
    (hM : 0 < M) (hp : p ∈ pieces M r s) :
    lastMax M (glue p) ↔ M-1 ∈ p.1.2.2.2 := by
  obtain ⟨hip,hpre,hblock⟩ := (by simpa only [pieces,Finset.mem_sigma,Finset.mem_product] using hp)
  rcases mem_indices.mp hip with ⟨hb,_,_,hsub,hcard⟩
  rcases mem_pairs.mp hpre with ⟨hU,_,_⟩
  rcases mem_irreducibles.mp hblock with ⟨hB,hD,he,hi⟩
  have hwhole := (mem_pairs.mp (Finset.mem_filter.mp (glue_mem hp)).1).1
  have hlen : (output p.2.1.1).length + (output p.2.2.1).length = M := by
    have := labelled_length hwhole
    simpa only [glue,output_append,List.length_append,Finset.card_range] using this
  have hpos : 0 < (output p.2.2.1).length := by rw [labelled_length hB,hcard]; omega
  have hmem : M-1 ∈ output (glue p).1 := by
    apply (output_perm _).mem_iff.mpr
    have : M-1 ∈ support (glue p).1 := by rw [support_eq hwhole]; exact Finset.mem_range.mpr (by omega)
    simpa [support] using this
  constructor
  · intro hl
    by_contra hm
    have hnotB : M-1 ∉ output p.2.2.1 := by
      intro hx
      have : M-1 ∈ support p.2.2.1 := by simpa [support] using (output_perm _).mem_iff.mp hx
      rw [support_eq hB] at this; exact hm this
    have hmemU : M-1 ∈ output p.2.1.1 := by
      simpa only [glue,output_append,List.mem_append,or_false,hnotB] using hmem
    have hidx := List.idxOf_lt_length_of_mem hmemU
    dsimp [lastMax,glue] at hl
    rw [output_append,List.idxOf_append] at hl
    simp only [hmemU,ite_true] at hl
    omega
  · intro hm
    have hnotU : M-1 ∉ output p.2.1.1 := by
      intro hx
      have : M-1 ∈ support p.2.1.1 := by simpa [support] using (output_perm _).mem_iff.mp hx
      rw [support_eq hU] at this
      exact (Finset.mem_sdiff.mp this).2 hm
    have ht := labelled_max_last hB hD hsub hm he hi
    dsimp [lastMax,glue]
    rw [output_append,List.idxOf_append]
    simp only [hnotU,ite_false]
    omega

def fixedPieces (M r s : ℕ) := (pieces M r s).filter (fun p => M-1 ∈ p.1.2.2.2)
def fixedReducibles (M r s : ℕ) := (reducibles M r s).filter (lastMax M)

theorem fixedPieces_card (M r s : ℕ) (hM : 0 < M) :
    (fixedPieces M r s).card = (fixedReducibles M r s).card := by
  apply Finset.card_bij (fun p _ => glue p)
  · intro p hp
    obtain ⟨hp,hm⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨glue_mem hp,(glue_last_iff hM hp).mpr hm⟩
  · intro p hp q hq he
    exact glue_injective (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  · intro q hq
    obtain ⟨hq,hm⟩ := Finset.mem_filter.mp hq
    obtain ⟨p,hp,he⟩ := glue_surjective hq hM
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,(glue_last_iff hM hp).mp (he.symm ▸ hm)⟩,he⟩
end StackSort.Fixed6
