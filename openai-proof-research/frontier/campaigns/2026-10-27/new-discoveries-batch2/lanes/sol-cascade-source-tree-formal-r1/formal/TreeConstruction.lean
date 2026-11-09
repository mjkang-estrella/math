import SourceDefs
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
attribute [local instance] Classical.propDecidable

def alternating (i : ℕ) : Bool := decide (i % 2 = 1)
def spine (n : ℕ) : Word := List.ofFn (fun i : Fin n => alternating i)
def anchor (k : ℕ) : Word := spine (2*k+1) ++ [false]
def constructionInternal : Set Word := {w | (∃ n, w = spine n) ∨
  ∃ k, 1 ≤ k ∧ anchor k <+: w ∧ w.length < depth k}
def constructionNodes : Set Word := {w | w ∈ constructionInternal ∨
  ∃ u a, u ∈ constructionInternal ∧ w = u ++ [a]}

@[simp] theorem spine_length (n : ℕ) : (spine n).length = n := by simp [spine]
@[simp] theorem anchor_length (k : ℕ) : (anchor k).length = 2*k+2 := by
  simp [anchor];

theorem spine_prefix {m n : ℕ} (h : m ≤ n) : spine m <+: spine n := by
  apply List.prefix_iff_getElem.mpr
  exact ⟨by simpa using h, by intros; simp [spine]⟩

theorem prefix_spine {u : Word} {n : ℕ} (h : u <+: spine n) : u = spine u.length := by
  have hs := spine_prefix (show u.length ≤ n by simpa using h.length_le)
  exact (List.prefix_of_prefix_length_le h hs (by simp)).eq_of_length (by simp)

theorem spine_succ (n : ℕ) : spine (n+1) = spine n ++ [alternating n] := by
  unfold spine
  rw [List.ofFn_succ_last]
  rfl

theorem spine_even (k : ℕ) : spine (2*k) = (List.replicate k [false,true]).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, spine_succ, spine_succ, ih]
    simp [alternating, List.replicate_succ', List.flatten_append, List.append_assoc]

theorem anchor_literal (k : ℕ) : anchor k =
    (List.replicate k [false,true]).flatten ++ [false,false] := by
  rw [anchor, spine_succ, spine_even]
  simp [alternating, List.append_assoc]

-- Any proper prefix of an anchor is on the alternating spine.
theorem prefix_anchor {u : Word} {k : ℕ} (h : u <+: anchor k) :
    u = anchor k ∨ u = spine u.length := by
  by_cases he : u.length = (anchor k).length
  · exact Or.inl (h.eq_of_length he)
  · right
    apply prefix_spine
    exact List.prefix_of_prefix_length_le h
      (show spine (2*k+1) <+: anchor k from ⟨[false], rfl⟩)
      (by have := h.length_le; simp only [anchor_length, spine_length] at *; omega)

theorem constructionInternal_prefix : PrefixClosed constructionInternal := by
  intro u w hu hw
  rcases hw with ⟨n, rfl⟩ | ⟨k, hk, ha, hd⟩
  · exact Or.inl ⟨u.length, prefix_spine hu⟩
  · rcases List.prefix_or_prefix_of_prefix hu ha with h | h
    · rcases prefix_anchor h with h | h
      · exact Or.inr ⟨k, hk, by rw [h], by have := hu.length_le; omega⟩
      · exact Or.inl ⟨u.length, h⟩
    · exact Or.inr ⟨k, hk, h, by have := hu.length_le; omega⟩

-- Saturation of a prefix-closed set of proposed internal nodes.
theorem constructionNodes_prefix : PrefixClosed constructionNodes := by
  intro u w hu hw
  rcases hw with hw | ⟨v, a, hv, rfl⟩
  · exact Or.inl (constructionInternal_prefix hu hw)
  · by_cases hlen : u.length ≤ v.length
    · exact Or.inl (constructionInternal_prefix
        (List.prefix_of_prefix_length_le hu ⟨[a], rfl⟩ hlen) hv)
    · have he : u = v ++ [a] := hu.eq_of_length (by
        have := hu.length_le; simp only [List.length_append, List.length_singleton] at *; omega)
      exact Or.inr ⟨v, a, hv, he⟩

theorem construction_internal_exact (w : Word) :
    Internal constructionNodes w ↔ w ∈ constructionInternal := by
  constructor
  · rintro ⟨a, h | ⟨v, b, hv, he⟩⟩
    · exact constructionInternal_prefix ⟨[a], rfl⟩ h
    · have : w = v := by
        have hl := congrArg List.length he
        simp only [List.length_append, List.length_singleton] at hl
        exact (List.prefix_of_prefix_length_le
          (show w <+: w ++ [a] from ⟨[a], rfl⟩)
          (show v <+: w ++ [a] from he ▸ ⟨[b], rfl⟩) (by omega)).eq_of_length (by omega)
      simpa [this] using hv
  · intro h
    exact ⟨false, Or.inr ⟨w, false, h, rfl⟩⟩

theorem construction_root_internal : Internal constructionNodes [] := by
  rw [construction_internal_exact]
  exact Or.inl ⟨0, rfl⟩

theorem construction_saturated (w : Word) (h : Internal constructionNodes w)
    (a : Bool) : w ++ [a] ∈ constructionNodes :=
  Or.inr ⟨w, a, (construction_internal_exact w).mp h, rfl⟩

-- Source's literal shift condition, without any tree or saturation assumption on S.
theorem short_shift_subsets (T : Set Word)
    (hstarts : ∀ w ∈ T, 3 ≤ w.length → [false,true] <+: w)
    (hforbid : ∀ a : Bool, [true,a] ∉ T)
    (S : Set Word) (hsub : S ⊆ T) (hp : PrefixClosed S) (hs : ShiftClosed S) :
    ∀ w ∈ S, w.length ≤ 2 := by
  intro w hw
  by_contra h
  have hl : 3 ≤ w.length := by omega
  have h01 := hstarts w (hsub hw) hl
  have he : ∃ a v, w = false :: true :: a :: v := by
    rcases h01 with ⟨v, rfl⟩
    cases v with
    | nil => simp at hl
    | cons a v => exact ⟨a,v,rfl⟩
  rcases he with ⟨a,v,rfl⟩
  have h3 : [false,true,a] ∈ S := hp ⟨v,rfl⟩ hw
  have h2 := hs _ h3
  exact hforbid a (hsub (by simpa using h2))

theorem finite_shift_subsets (T : Set Word)
    (hstarts : ∀ w ∈ T, 3 ≤ w.length → [false,true] <+: w)
    (hforbid : ∀ a : Bool, [true,a] ∉ T)
    (S : Set Word) (hsub : S ⊆ T) (hp : PrefixClosed S) (hs : ShiftClosed S) : S.Finite :=
  (List.finite_length_le Bool 2).subset (short_shift_subsets T hstarts hforbid S hsub hp hs)

@[simp] theorem spine_two : spine 2 = [false,true] := rfl
@[simp] theorem spine_one : spine 1 = [false] := rfl

theorem internal_begins01 {w : Word} (h : w ∈ constructionInternal)
    (hl : 2 ≤ w.length) : [false,true] <+: w := by
  rcases h with ⟨n,rfl⟩ | ⟨k,hk,ha,_⟩
  · exact spine_prefix (by simpa using hl)
  · exact (spine_prefix (show 2 ≤ 2*k+1 by omega)).trans
      ((show spine (2*k+1) <+: anchor k from ⟨[false],rfl⟩).trans ha)

theorem nodes_begins01 (w : Word) (h : w ∈ constructionNodes)
    (hl : 3 ≤ w.length) : [false,true] <+: w := by
  rcases h with h | ⟨u,a,hu,rfl⟩
  · exact internal_begins01 h (by omega)
  · exact (internal_begins01 hu (by simp only [List.length_append,
      List.length_singleton] at hl; omega)).trans ⟨[a],rfl⟩

theorem internal_begins0 {w : Word} (h : w ∈ constructionInternal)
    (hl : 1 ≤ w.length) : [false] <+: w := by
  rcases h with ⟨n,rfl⟩ | ⟨k,hk,ha,_⟩
  · exact spine_prefix (by simpa using hl)
  · exact (spine_prefix (show 1 ≤ 2*k+1 by omega)).trans
      ((show spine (2*k+1) <+: anchor k from ⟨[false],rfl⟩).trans ha)

theorem nodes_forbid1child (a : Bool) : [true,a] ∉ constructionNodes := by
  rintro (h | ⟨u,b,hu,he⟩)
  · have hp := internal_begins0 h (by simp)
    simp at hp
  · have hl : u.length = 1 := by have := congrArg List.length he; simp at this; omega
    have hp := (internal_begins0 hu (by omega)).trans
      (show u <+: [true,a] from he ▸ ⟨[b],rfl⟩)
    simp at hp

theorem construction_no_infinite_shift_subtree (S : Set Word)
    (hsub : S ⊆ constructionNodes) (hp : PrefixClosed S) (hs : ShiftClosed S) :
    S.Finite := finite_shift_subsets constructionNodes nodes_begins01 nodes_forbid1child S hsub hp hs

theorem one_leaf : FiniteContext constructionNodes [true] := by
  refine ⟨Or.inr ⟨[],true,Or.inl ⟨0,rfl⟩,rfl⟩, ?_⟩
  rintro ⟨a,ha⟩
  exact nodes_forbid1child a ha

theorem zerozero_leaf : FiniteContext constructionNodes [false,false] := by
  refine ⟨Or.inr ⟨[false],false,Or.inl ⟨1,rfl⟩,rfl⟩, ?_⟩
  rw [construction_internal_exact]
  intro h
  have hp := internal_begins01 h (by simp)
  simp at hp

def infinitePrefix (b : InfiniteWord) (n : ℕ) : Word := List.ofFn (fun i : Fin n => b i)
@[simp] theorem infinitePrefix_length (b : InfiniteWord) (n : ℕ) :
    (infinitePrefix b n).length = n := by simp [infinitePrefix]

theorem infinitePrefix_prefix (b : InfiniteWord) {m n : ℕ} (h : m ≤ n) :
    infinitePrefix b m <+: infinitePrefix b n := by
  apply List.prefix_iff_getElem.mpr
  exact ⟨by simpa using h, by intros; simp [infinitePrefix]⟩

theorem branch_internal (b : InfiniteWord) (hb : InfiniteContext constructionNodes b) (n : ℕ) :
    infinitePrefix b n ∈ constructionInternal := by
  rw [← construction_internal_exact]
  have h : Internal constructionNodes (infinitePrefix b n) := by
    refine ⟨b n, ?_⟩
    have he : infinitePrefix b n ++ [b n] = infinitePrefix b (n+1) := by
      unfold infinitePrefix
      rw [List.ofFn_succ_last]
      rfl
    rw [he]
    exact hb (n+1)
  exact h

-- A divergent prefix bounds the index of every bush containing any extension.
theorem divergent_bush_bound {u : Word} {n k : ℕ}
    (hdiv : u ≠ spine n) (hul : u.length = n)
    (ha : anchor k <+: u) : 2*k+1 < n := by
  by_contra h
  have hp : u <+: spine (2*k+1) := List.prefix_of_prefix_length_le
    (List.prefix_refl u) (show spine (2*k+1) <+: u from
      (show spine (2*k+1) <+: anchor k from ⟨[false],rfl⟩).trans ha)
    (by simp [hul]; omega)
  exact hdiv (hul ▸ prefix_spine hp)

-- Bound all bush indices by a divergent prefix, then contradict one longer branch prefix.
theorem unique_infinite_branch (b : InfiniteWord)
    (hb : InfiniteContext constructionNodes b) : b = alternating := by
  have heq : ∀ n, infinitePrefix b n = spine n := by
    intro n
    by_contra hdiv
    let B := ∑ k ∈ Finset.range (n+1), depth k
    let m := max n (B+1)
    have hm : n ≤ m := le_max_left _ _
    have hi := branch_internal b hb m
    rcases hi with ⟨j,hj⟩ | ⟨k,hk,ha,hd⟩
    · have hjm : j = m := by have := congrArg List.length hj; simpa using this.symm
      have hp : infinitePrefix b n <+: spine m := hjm ▸ hj ▸ infinitePrefix_prefix b hm
      exact hdiv (by simpa using prefix_spine hp)
    · have hlong : 2*k+1 < n := by
        by_contra hh
        have hp : infinitePrefix b n <+: spine (2*k+1) :=
          List.prefix_of_prefix_length_le (infinitePrefix_prefix b hm)
            ((show spine (2*k+1) <+: anchor k from ⟨[false],rfl⟩).trans ha)
            (by simp; omega)
        exact hdiv (by simpa using prefix_spine hp)
      have hkb : depth k ≤ B := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
      have hmm : B+1 ≤ m := le_max_right _ _
      simp only [infinitePrefix_length] at hd
      omega
  funext i
  have h := congrArg (fun w : Word => w[i]?) (heq (i+1))
  simpa only [infinitePrefix, spine, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self i),
    Option.some.injEq] using h

theorem alternating_branch : InfiniteContext constructionNodes alternating := by
  intro n
  exact Or.inl (Or.inl ⟨n,rfl⟩)

def sourceTree : SourceContextTree where
  nodes := constructionNodes
  prefix_closed := constructionNodes_prefix
  root_internal := construction_root_internal
  saturated := construction_saturated
  countable_branches := (Set.countable_singleton alternating).mono (by
    intro b hb
    exact Set.mem_singleton_iff.mpr (unique_infinite_branch b hb))

theorem sourceTree_no_infinite_stable (S : SourceContextTree)
    (hsub : S.nodes ⊆ sourceTree.nodes) (hs : ShiftClosed S.nodes) : S.nodes.Finite :=
  construction_no_infinite_shift_subtree S.nodes hsub S.prefix_closed hs

theorem sourceTree_no_infinite_stable_exists :
    ¬ ∃ S : SourceContextTree, S.nodes ⊆ sourceTree.nodes ∧
      ShiftClosed S.nodes ∧ S.nodes.Infinite := by
  rintro ⟨S,hsub,hs,hi⟩
  exact hi (sourceTree_no_infinite_stable S hsub hs)

theorem one_contextAlphaLIS : ContextAlphaLIS sourceTree [true] :=
  ⟨[true], one_leaf, alphaLIS_singleton sourceTree true⟩
end CascadeRate
