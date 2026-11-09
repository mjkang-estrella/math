import StackSortLabels4
import StackSortCut4

namespace StackSort.Cut5
open Seeds2 Shuffle3 Round4
open Classical

/-- The exact label set retained by a tuple, independent of its word boundaries. -/
def support (F : List (List ℕ)) : Finset ℕ := F.flatten.toFinset

theorem mem_labelledTuples {A : Finset ℕ} {r : ℕ} {F : List (List ℕ)} :
    F ∈ labelledTuples A r ↔
      F.flatten.Perm A.sort ∧ F.length = r ∧ NonemptyWords F := by
  simp only [labelledTuples, Finset.mem_biUnion, mem_sections, mem_labelWords]
  constructor
  · rintro ⟨w, hw, hl, he, hn⟩
    exact ⟨he ▸ hw, hl, hn⟩
  · rintro ⟨hw, hl, hn⟩
    exact ⟨F.flatten, hw, hl, rfl, hn⟩

theorem support_eq {A : Finset ℕ} {r : ℕ} {F : List (List ℕ)}
    (hF : F ∈ labelledTuples A r) : support F = A := by
  have h := (mem_labelledTuples.mp hF).1
  ext x; simpa [support] using h.mem_iff

theorem labelled_nodup {A : Finset ℕ} {r : ℕ} {F : List (List ℕ)}
    (hF : F ∈ labelledTuples A r) : F.flatten.Nodup :=
  (mem_labelledTuples.mp hF).1.nodup_iff.mpr (Finset.sort_nodup _ _)

theorem support_collision {F G : List (List ℕ)} (he : output F = output G) :
    support F = support G := by
  have h := (output_perm F).symm.trans (he ▸ output_perm G)
  ext x; simpa [support] using h.mem_iff

theorem support_append (F G : List (List ℕ)) :
    support (F ++ G) = support F ∪ support G := by
  simp [support]

/-- A collision of complete tuples is exactly a collision on their prescribed labels. -/
theorem labelledPairs_range (M r s : ℕ) :
    labelledPairs (Finset.range M) r s =
      ((tuples M r ×ˢ tuples M s).filter (fun p => output p.1 = output p.2)) := by
  have ht : ∀ t, labelledTuples (Finset.range M) t = tuples M t := by
    intro t
    ext F
    simp only [mem_labelledTuples, mem_tuples, mem_words]
    simp [NonemptyWords]
  simp only [labelledPairs, ht]

end StackSort.Cut5

namespace StackSort.Cut5
open Seeds2 Shuffle3 Round4
open Classical

theorem labelled_of_nodup {F : List (List ℕ)} (hn : F.flatten.Nodup)
    (hw : NonemptyWords F) : F ∈ labelledTuples (support F) F.length := by
  apply mem_labelledTuples.mpr
  refine ⟨?_, rfl, hw⟩
  apply List.perm_of_nodup_nodup_toFinset_eq hn (Finset.sort_nodup _ _)
  simp [support]

theorem labelled_split {A : Finset ℕ} {r : ℕ} {U V : List (List ℕ)}
    (h : U ++ V ∈ labelledTuples A r) :
    U ∈ labelledTuples (support U) U.length ∧
    V ∈ labelledTuples (support V) V.length ∧
    Disjoint (support U) (support V) ∧ support U = A \ support V := by
  have hn := labelled_nodup h
  rw [List.flatten_append, List.nodup_append] at hn
  have hw := nonemptyWords_append.mp (mem_labelledTuples.mp h).2.2
  have hd : Disjoint (support U) (support V) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact hn.2.2 x (by simpa [support] using hx) x (by simpa [support] using hy) rfl
  refine ⟨labelled_of_nodup hn.1 hw.1, labelled_of_nodup hn.2.1 hw.2, hd, ?_⟩
  have hs := support_eq h
  rw [support_append] at hs
  rw [← hs]
  exact (Finset.union_sdiff_cancel_right hd).symm

theorem labelled_append {A B : Finset ℕ} {r s : ℕ} {U V : List (List ℕ)}
    (hU : U ∈ labelledTuples A r) (hV : V ∈ labelledTuples B s)
    (hd : Disjoint A B) : U ++ V ∈ labelledTuples (A ∪ B) (r+s) := by
  have hnU := labelled_nodup hU
  have hnV := labelled_nodup hV
  have hn : (U ++ V).flatten.Nodup := by
    rw [List.flatten_append, List.nodup_append]
    refine ⟨hnU, hnV, ?_⟩
    intro x hx y hy he
    subst y
    apply Finset.disjoint_left.mp hd
    · have : x ∈ support U := by simpa [support] using hx
      simpa [support_eq hU] using this
    · have : x ∈ support V := by simpa [support] using hy
      simpa [support_eq hV] using this
  have hw := nonemptyWords_append.mpr ⟨(mem_labelledTuples.mp hU).2.2,
    (mem_labelledTuples.mp hV).2.2⟩
  have hm := labelled_of_nodup hn hw
  rw [support_append, support_eq hU, support_eq hV] at hm
  simpa only [List.length_append, (mem_labelledTuples.mp hU).2.1,
    (mem_labelledTuples.mp hV).2.1] using hm

theorem labelled_length {A : Finset ℕ} {r : ℕ} {F : List (List ℕ)}
    (h : F ∈ labelledTuples A r) : (output F).length = A.card := by
  rw [output_length]
  simpa using (mem_labelledTuples.mp h).1.length_eq

theorem words_length_le_output {F : List (List ℕ)} (h : NonemptyWords F) :
    F.length ≤ (output F).length := by
  rw [output_length]
  induction F with
  | nil => simp
  | cons w F ih =>
    have hw := List.length_pos_iff.mpr (h w (by simp))
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

end StackSort.Cut5
