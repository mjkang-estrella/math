import TreeConstruction
import DepthAnalysis

set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

abbrev SelectedCode (k : ℕ) := Fin (blockCount k) → Fin (k-2) → Bool

def selectedBlocks (k : ℕ) (u : SelectedCode k) : List Word :=
  List.ofFn (fun i => [true,true] ++ List.ofFn (u i))

def selectedWord (k : ℕ) (u : SelectedCode k) : Word :=
  anchor k ++ (selectedBlocks k u).flatten ++
    List.replicate (tailRemainder k + terminalLength k) true

theorem selectedBlocks_length (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    (selectedBlocks k u).flatten.length = blockCount k * k := by
  have he : k-2+1+1 = k := by omega
  simp [selectedBlocks, List.length_flatten, List.map_ofFn, Function.comp_def, he]

theorem selectedWord_length (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    (selectedWord k u).length = depth k := by
  simp only [selectedWord, List.length_append, anchor_length,
    selectedBlocks_length k hk, List.length_replicate]
  have hd := decomposition k hk
  unfold anchorLength at hd
  omega

-- Equal-length chunk lists have a unique flattening.
theorem flatten_injective_fixed (n : ℕ) (xs ys : List Word)
    (hx : ∀ x ∈ xs, x.length = n) (hy : ∀ y ∈ ys, y.length = n)
    (hl : xs.length = ys.length) (he : xs.flatten = ys.flatten) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hxn := hx x (by simp)
      have hyn := hy y (by simp)
      have hxy : x = y := by
        have hh := congrArg (List.take n) he
        rw [List.flatten_cons, List.flatten_cons, ← hxn, List.take_left, hxn,
          ← hyn, List.take_left] at hh
        exact hh
      subst y
      have ht : xs.flatten = ys.flatten := List.append_cancel_left he
      have hr := ih ys (by intro a ha; exact hx a (by simp [ha]))
        (by intro a ha; exact hy a (by simp [ha])) (by simpa using hl) ht
      simp [hr]

theorem selectedWord_injective (k : ℕ) : Function.Injective (selectedWord k) := by
  intro u v he
  have hh : (selectedBlocks k u).flatten = (selectedBlocks k v).flatten :=
    List.append_cancel_left (List.append_cancel_right he)
  have blocksLen : ∀ z : SelectedCode k, ∀ x ∈ selectedBlocks k z,
      x.length = 2 + (k-2) := by
    intro z x hx
    simp only [selectedBlocks, List.mem_ofFn] at hx
    obtain ⟨i,rfl⟩ := hx
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn]
  have hb := flatten_injective_fixed (2+(k-2)) _ _ (blocksLen u) (blocksLen v)
    (by simp [selectedBlocks]) hh
  have hf : (fun i => [true,true] ++ List.ofFn (u i)) =
      (fun i => [true,true] ++ List.ofFn (v i)) := List.ofFn_injective hb
  funext i
  exact List.ofFn_injective (List.append_cancel_left (congrFun hf i))

theorem selectedCode_card (k : ℕ) : Fintype.card (SelectedCode k) = 2 ^ freeCount k := by
  simp [SelectedCode, freeCount, ← pow_mul]

theorem anchor_not_prefix_spine (k n : ℕ) : ¬ anchor k <+: spine n := by
  intro hp
  have hl := hp.length_le
  simp only [anchor_length, spine_length] at hl
  have he := (List.prefix_iff_getElem.mp hp).2 (2*k+1) (by simp)
  simp [anchor, spine, alternating] at he

theorem anchor_prefix_index {j k : ℕ} {w : Word}
    (hj : anchor j <+: w) (hk : anchor k <+: w) : j = k := by
  have step : ∀ a b : ℕ, a < b → ¬ anchor a <+: anchor b := by
    intro a b hab hp
    have he := (List.prefix_iff_getElem.mp hp).2 (2*a+1) (by simp)
    simp only [anchor, List.getElem_append] at he
    simp [spine, alternating, show 2*a+1 < 2*b+1 by omega] at he
  rcases lt_trichotomy j k with h | h | h
  · rcases List.prefix_or_prefix_of_prefix hj hk with hp | hp
    · exact (step j k h hp).elim
    · have := hp.length_le; simp only [anchor_length] at this; omega
  · exact h
  · rcases List.prefix_or_prefix_of_prefix hj hk with hp | hp
    · have := hp.length_le; simp only [anchor_length] at this; omega
    · exact (step k j h hp).elim

theorem bottom_context {k : ℕ} (hk : 3 ≤ k) {w : Word}
    (ha : anchor k <+: w) (hl : w.length = depth k) :
    FiniteContext sourceTree.nodes w := by
  have hroom := room k hk
  have hlen : 0 < w.length := by rw [hl]; have := index_le_depth k; omega
  have hparent : w.take (w.length-1) ∈ constructionInternal := by
    right
    refine ⟨k, by omega, ?_, ?_⟩
    · apply List.prefix_iff_getElem.mpr
      refine ⟨?_, ?_⟩
      · simp only [List.length_take, anchor_length]
        unfold anchorLength terminalLength at hroom
        omega
      · intro i hi
        simpa using (List.prefix_iff_getElem.mp ha).2 i hi
    · simp only [List.length_take]; omega
  have hnode : w ∈ sourceTree.nodes := by
    have he := List.take_append_getElem (l := w) (i := w.length-1) (by omega)
    have ht : w.take (w.length-1) ++ [w[w.length-1]'(by omega)] = w := by
      simpa [show w.length-1+1=w.length by omega] using he
    exact ht ▸ Or.inr ⟨_,_,hparent,rfl⟩
  refine ⟨hnode, ?_⟩
  rw [show sourceTree.nodes = constructionNodes from rfl, construction_internal_exact]
  rintro (⟨n,he⟩ | ⟨j,_,hj,hd⟩)
  · exact anchor_not_prefix_spine k n (he ▸ ha)
  · have hjk := anchor_prefix_index hj ha
    subst j
    omega

theorem selectedWord_context (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    FiniteContext sourceTree.nodes (selectedWord k u) :=
  bottom_context hk ⟨(selectedBlocks k u).flatten ++
      List.replicate (tailRemainder k + terminalLength k) true,
      by simp [selectedWord, List.append_assoc]⟩
    (selectedWord_length k hk u)

-- Exact number of distinct literal words (including the zero-block case).
noncomputable def selectedFamily (k : ℕ) : Finset Word :=
  Finset.univ.image (selectedWord k)

theorem selectedFamily_card (k : ℕ) : (selectedFamily k).card = 2 ^ freeCount k := by
  rw [selectedFamily, Finset.card_image_of_injective _ (selectedWord_injective k)]
  simpa using selectedCode_card k

-- A repeated adjacent pair cannot occur inside an alternating spine prefix.
theorem spine_adjacent_ne (n i : ℕ) (hi : i+1 < n) :
    (spine n)[i]'(by simp; omega) ≠ (spine n)[i+1]'(by simp; omega) := by
  simp only [spine, List.getElem_ofFn, alternating, ne_eq, decide_eq_decide]
  omega

theorem equal_pair_blocks_spine {w : Word} {n i : ℕ}
    (hi : i+1 < n) (hwi : i+1 < w.length)
    (he : w[i]'(by omega) = w[i+1]) : ¬ spine n <+: w := by
  intro hp
  have hh := (List.prefix_iff_getElem.mp hp).2
  exact spine_adjacent_ne n i hi ((hh i (by simp; omega)).trans
    (he.trans (hh (i+1) (by simp; omega)).symm))

theorem pair_prefix_blocks_spine {w : Word} {n p : ℕ}
    (hn : p+1 < n) {a : Bool} (hp : [a,a] <+: w.drop p) : ¬ spine n <+: w := by
  have hl := hp.length_le
  simp only [List.length_cons, List.length_nil, List.length_drop] at hl
  have he := (List.prefix_iff_getElem.mp hp).2
  have h0 := he 0 (by simp)
  have h1 := he 1 (by simp)
  apply equal_pair_blocks_spine hn (by omega)
  simpa using h0.symm.trans h1

-- This generic lemma treats every number of blocks, every suffix position,
-- and arbitrary free block contents. It uses no finite enumeration.
theorem blocked_tail_no_spine (k : ℕ) (hk : 3 ≤ k) (xs : List Word)
    (hx : ∀ x ∈ xs, x.length = k ∧ [true,true] <+: x)
    (t : ℕ) (ht : 3 ≤ t) (i : ℕ) :
    ¬ spine (2*k) <+: (xs.flatten ++ List.replicate t true).drop i := by
  induction xs generalizing i with
  | nil =>
    simp only [List.flatten_nil, List.nil_append, List.drop_replicate]
    intro hp
    have hl := hp.length_le
    have he := (List.prefix_iff_getElem.mp hp).2 0 (by simp; omega)
    simp [spine, alternating] at he
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hxs : ∀ y ∈ xs, y.length = k ∧ [true,true] <+: y := by
      intro y hy; exact hx y (by simp [hy])
    let tail := xs.flatten ++ List.replicate t true
    have htail : [true,true] <+: tail := by
      cases xs with
      | nil =>
        refine List.prefix_iff_getElem.mpr ⟨by simp [tail]; omega, ?_⟩
        intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        have hj' : j=0 ∨ j=1 := by omega
        rcases hj' with rfl | rfl <;> simp [tail]
      | cons y ys =>
        exact (hxs y (by simp)).2.trans ⟨ys.flatten ++ List.replicate t true,
          by simp [tail, List.append_assoc]⟩
    simp only [List.flatten_cons, List.append_assoc]
    change ¬ spine (2*k) <+: (x ++ tail).drop i
    by_cases hik : k ≤ i
    · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hxx.1]
      exact ih hxs (i-k)
    · have hil : i < k := by omega
      apply pair_prefix_blocks_spine (p := k-i) (by omega)
      have he : ((x ++ tail).drop i).drop (k-i) = tail := by
        rw [List.drop_drop, show i+(k-i)=k by omega, ← hxx.1]
        simp
      rw [he]
      exact htail

def selectedTail (k : ℕ) (u : SelectedCode k) : Word :=
  (selectedBlocks k u).flatten ++ List.replicate (tailRemainder k + terminalLength k) true

theorem selectedTail_pair (k : ℕ) (u : SelectedCode k) :
    [true,true] <+: selectedTail k u := by
  have ht : 2 ≤ tailRemainder k + terminalLength k := by unfold terminalLength; omega
  unfold selectedTail selectedBlocks
  by_cases hb : blockCount k = 0
  · simp only [hb, List.ofFn_zero, List.flatten_nil, List.nil_append]
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simp; omega, ?_⟩
    intro i hi
    have : i=0 ∨ i=1 := by simp only [List.length_cons, List.length_nil] at hi; omega
    rcases this with rfl | rfl <;> simp
  · obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero hb
    simp only [hb, List.ofFn_succ, List.flatten_cons, List.append_assoc]
    exact ⟨_, rfl⟩

theorem selectedTail_no_spine (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) (i : ℕ) :
    ¬ spine (2*k) <+: (selectedTail k u).drop i := by
  apply blocked_tail_no_spine k hk (selectedBlocks k u) ?_
    (tailRemainder k + terminalLength k) (by unfold terminalLength; omega) i
  intro x hx
  simp only [selectedBlocks, List.mem_ofFn] at hx
  obtain ⟨j,rfl⟩ := hx
  exact ⟨by simp; omega, ⟨_, rfl⟩⟩

theorem selectedWord_shift_no_spine (k : ℕ) (hk : 3 ≤ k)
    (u : SelectedCode k) (i : ℕ) (hi : 0 < i) :
    ¬ spine (2*k) <+: (selectedWord k u).drop i := by
  have hw : selectedWord k u = anchor k ++ selectedTail k u := by
    simp [selectedWord, selectedTail, List.append_assoc]
  rw [hw]
  by_cases hil : 2*k+2 ≤ i
  · rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append, anchor_length]
    exact selectedTail_no_spine k hk u _
  · have hib : i ≤ 2*k+1 := by omega
    by_cases hie : i = 2*k+1
    · subst i
      apply pair_prefix_blocks_spine (p := 1) (by omega)
      rw [List.drop_drop, show 2*k+1+1 = 2*k+2 by omega, ← anchor_length k]
      simpa using selectedTail_pair k u
    · by_cases hi1 : i=1
      · subst i
        intro hp
        have he := (List.prefix_iff_getElem.mp hp).2 0 (by simp; omega)
        have hl : 1 < (anchor k).length := by simp
        have he1 : (anchor k)[1] = true := by
          have hp2 : spine 2 <+: anchor k := (spine_prefix (show 2 ≤ 2*k+1 by omega)).trans ⟨[false],rfl⟩
          exact ((List.prefix_iff_getElem.mp hp2).2 1 (by simp)).symm
        have he2 : ((anchor k ++ selectedTail k u).drop 1)[0] = true := by
          simpa [List.getElem_append_left hl] using he1
        simp only [spine, List.getElem_ofFn, alternating] at he
        rw [he2] at he
        contradiction
      · apply pair_prefix_blocks_spine (p := 2*k-i) (a := false) (by omega)
        rw [List.drop_drop, show i+(2*k-i)=2*k by omega]
        rw [anchor_literal]
        have he : ((List.replicate k [false,true]).flatten).length = 2*k := by simp; omega
        rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega)]
        simp only [List.nil_append, he, Nat.sub_self, List.drop_zero]
        exact ⟨_, rfl⟩

theorem selectedWord_short_suffix (k : ℕ) (u : SelectedCode k) (i : ℕ)
    (hi : (selectedWord k u).length - i ≤ tailRemainder k + terminalLength k) :
    (selectedWord k u).drop i =
      List.replicate ((selectedWord k u).length - i) true := by
  unfold selectedWord at *
  simp only [List.length_append, List.length_replicate] at *
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp only [List.length_append]; omega), List.nil_append,
    List.drop_replicate]
  simp only [List.length_append]
  congr 1
  omega

theorem selectedWord_suffix_not_spine (k : ℕ) (_hk : 3 ≤ k)
    (u : SelectedCode k) (i : ℕ) (hi : i < (selectedWord k u).length) :
    ¬ ∃ n, (selectedWord k u).drop i = spine n := by
  rintro ⟨n,hn⟩
  have hl : (selectedWord k u).length - i = n := by
    have hh := congrArg List.length hn
    simpa using hh
  have ht : 3 ≤ tailRemainder k + terminalLength k := by unfold terminalLength; omega
  by_cases hn2 : n < 2
  · have he := selectedWord_short_suffix k u i (by omega)
    rw [hn] at he
    have hh := congrArg (fun w : Word => w[0]?) he
    rw [hl] at hh
    simp [spine, alternating, show 0 < n by omega] at hh
  · have hp : [true,true] <+: ((selectedWord k u).drop i).drop (n-2) := by
      rw [List.drop_drop, selectedWord_short_suffix k u (i+(n-2)) (by omega)]
      have he : (selectedWord k u).length - (i+(n-2)) = 2 := by omega
      simp [he]
    exact pair_prefix_blocks_spine (n := n) (by omega) hp
      (by rw [hn])

theorem selectedWord_suffix_noninternal (k : ℕ) (hk : 3 ≤ k)
    (u : SelectedCode k) (i : ℕ) (hi : 0 < i)
    (hil : i < (selectedWord k u).length) :
    ¬ Internal sourceTree.nodes ((selectedWord k u).drop i) := by
  rw [show sourceTree.nodes = constructionNodes from rfl, construction_internal_exact]
  rintro (hs | ⟨j,hj,ha,hd⟩)
  · exact selectedWord_suffix_not_spine k hk u i hil hs
  · by_cases hjk : j < k
    · have hdepth : depth j ≤ depth (k-1) := depth_strictMono.monotone (by omega)
      have hshort : (selectedWord k u).length - i ≤ tailRemainder k + terminalLength k := by
        simp only [List.length_drop] at hd
        unfold terminalLength
        omega
      rw [selectedWord_short_suffix k u i hshort] at ha
      have hp := (spine_prefix (show 1 ≤ 2*j+1 by omega)).trans
        ((show spine (2*j+1) <+: anchor j from ⟨[false],rfl⟩).trans ha)
      have he := (List.prefix_iff_getElem.mp hp).2 0 (by simp)
      simp [spine, alternating] at he
    · have hp := (spine_prefix (show 2*k ≤ 2*j+1 by omega)).trans
        ((show spine (2*j+1) <+: anchor j from ⟨[false],rfl⟩).trans ha)
      exact selectedWord_shift_no_spine k hk u i hi hp

theorem selectedWord_lisIndex (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    lisIndex sourceTree (selectedWord k u) = (selectedWord k u).length := by
  have hl : 0 < (selectedWord k u).length := by
    rw [selectedWord_length k hk u]; have := index_le_depth k; omega
  have hs := lisIndex_spec sourceTree (List.length_pos_iff.mp hl)
  by_contra he
  exact selectedWord_suffix_noninternal k hk u _ hs.1 (by omega) hs.2.1

theorem selectedWord_lis (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    lis sourceTree (selectedWord k u) = [] := by
  simp [lis, selectedWord_lisIndex k hk u]

theorem selectedWord_alphaLIS (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    alphaLIS sourceTree (selectedWord k u) = [true] := by
  unfold alphaLIS
  rw [selectedWord_lisIndex k hk u, selectedWord_short_suffix]
  · have hl : 0 < (selectedWord k u).length := by
      rw [selectedWord_length k hk u]; have := index_le_depth k; omega
    simp [show (selectedWord k u).length - ((selectedWord k u).length-1)=1 by omega]
  · unfold terminalLength; omega
end CascadeRate
