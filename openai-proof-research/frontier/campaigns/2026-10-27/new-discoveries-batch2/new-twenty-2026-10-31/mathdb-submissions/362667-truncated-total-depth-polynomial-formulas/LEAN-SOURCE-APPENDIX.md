# Lean source appendix

Modules appear in import order.

### `DMZTrees.lean`

```lean
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset
open scoped BigOperators

namespace DMZ

/-- Rooted ordered trees. The children are stored in their traversal order. -/
inductive PTree where
  | node : List PTree → PTree

mutual
  def encode : PTree → BinaryTree Unit
    | .node ts => encodeChildren ts
  def encodeChildren : List PTree → BinaryTree Unit
    | [] => .nil
    | t :: ts => .node () (encode t) (encodeChildren ts)
end

/-- The empty binary tree is the root with no children.
A binary node records the first child and the remainder of the child list. -/
def childrenOf : BinaryTree Unit → List PTree
  | .nil => []
  | .node _ l r => .node (childrenOf l) :: childrenOf r

def decode (b : BinaryTree Unit) : PTree := .node (childrenOf b)

@[simp] theorem encode_decode (b : BinaryTree Unit) : encode (decode b) = b := by
  induction b using BinaryTree.unitRecOn with
  | base => rfl
  | ind l r il ir =>
    change BinaryTree.node () (encode (decode l)) (encode (decode r)) =
      BinaryTree.node () l r
    rw [il, ir]

mutual
  theorem decode_encode (t : PTree) : decode (encode t) = t := by
    cases t with
    | node ts =>
      change PTree.node (childrenOf (encodeChildren ts)) = .node ts
      rw [children_encode ts]
  theorem children_encode (ts : List PTree) : childrenOf (encodeChildren ts) = ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      change decode (encode t) :: childrenOf (encodeChildren ts) = t :: ts
      rw [decode_encode t, children_encode ts]
end

def decodeEmbedding : BinaryTree Unit ↪ PTree :=
  ⟨decode, Function.LeftInverse.injective encode_decode⟩

mutual
  /-- Count one edge per child, plus the edges in that child's subtree. -/
  def edges : PTree → ℕ
    | .node ts => childEdges ts
  def childEdges : List PTree → ℕ
    | [] => 0
    | t :: ts => 1 + edges t + childEdges ts
end

theorem edges_decode (b : BinaryTree Unit) : edges (decode b) = b.numNodes := by
  induction b using BinaryTree.unitRecOn with
  | base => rfl
  | ind l r il ir =>
    change 1 + edges (decode l) + edges (decode r) = l.numNodes + r.numNodes + 1
    rw [il, ir]
    omega

def trees (n : ℕ) : Finset PTree :=
  (BinaryTree.treesOfNumNodesEq n).map decodeEmbedding

@[simp] theorem mem_trees {n : ℕ} {t : PTree} : t ∈ trees n ↔ edges t = n := by
  simp only [trees, Finset.mem_map, BinaryTree.mem_treesOfNumNodesEq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (edges_decode b).trans hb
  · intro ht
    refine ⟨encode t, ?_, decode_encode t⟩
    rw [← edges_decode, decode_encode, ht]

mutual
  /-- Traversal depths in pre-order, starting at the root at depth zero. -/
  def preorderDepths : PTree → List ℕ
    | .node ts => 0 :: forestDepths ts
  def forestDepths : List PTree → List ℕ
    | [] => []
    | t :: ts => (preorderDepths t).map Nat.succ ++ forestDepths ts
end

def dfsScore (k : ℕ) : ℕ := k

def dfsTruncScore (h : ℕ) (ds : List ℕ) (k : ℕ) : ℕ :=
  ((ds.take k).filter (· ≤ h)).length

def scoreSum (h : ℕ) (ds : List ℕ) (score : ℕ → ℕ) : ℕ :=
  ∑ k ∈ range ds.length, if ds[k]? = some h then score k else 0

def totalD (n h : ℕ) : ℕ :=
  ∑ t ∈ trees n, scoreSum h (preorderDepths t) dfsScore

def totalDTrunc (n h : ℕ) : ℕ :=
  ∑ t ∈ trees n, scoreSum h (preorderDepths t) (dfsTruncScore h (preorderDepths t))

def chooseZ (n : ℕ) (k : ℤ) : ℤ :=
  if k < 0 then 0 else n.choose k.toNat

def rising (n d : ℕ) : ℤ := n.ascFactorial d

theorem rising_pos {n : ℕ} (hn : 0 < n) (d : ℕ) : 0 < rising n d := by
  induction d with
  | zero => simp [rising]
  | succ d ih =>
    simpa [rising, Nat.ascFactorial_succ, Int.natCast_mul] using
      mul_pos (show (0 : ℤ) < ((n + d : ℕ) : ℤ) by omega) ih

end DMZ
```

### `DMZScores.lean`

```lean
import DMZTrees
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

namespace DMZ

/-- Number of ordered pairs of positions, first satisfying `p` and later satisfying `q`. -/
def pairCount (p q : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | a :: as => pairCount p q as + if p a then as.countP q else 0

theorem countP_indices (q : ℕ → Bool) (xs : List ℕ) :
    (∑ i ∈ range xs.length, if (xs[i]?).any q then 1 else 0) = xs.countP q := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, sum_range_succ', List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.any_some, List.countP_cons, ih]

theorem pairCount_indices (p q : ℕ → Bool) (xs : List ℕ) :
    (∑ i ∈ range xs.length, if (xs[i]?).any q then (xs.take i).countP p else 0) =
      pairCount p q xs := by
  induction xs with
  | nil => simp [pairCount]
  | cons a as ih =>
    simp only [List.length_cons, sum_range_succ', List.getElem?_cons_succ, List.take_succ_cons,
      List.countP_cons, List.take_zero, List.countP_nil, ite_self, add_zero, pairCount]
    calc
      _ = (∑ i ∈ range as.length, ((if (as[i]?).any q then (as.take i).countP p else 0) +
          (if (as[i]?).any q then (if p a then 1 else 0) else 0))) := by
        apply sum_congr rfl
        intro i _
        split <;> rfl
      _ = _ := by
        rw [sum_add_distrib, ih]
        by_cases h : p a
        · simp only [h, ite_true, countP_indices]
        · simp [h]

theorem pairCount_append (p q : ℕ → Bool) (xs ys : List ℕ) :
    pairCount p q (xs ++ ys) =
      pairCount p q xs + pairCount p q ys + xs.countP p * ys.countP q := by
  induction xs with
  | nil => simp [pairCount]
  | cons a as ih =>
    simp only [List.cons_append, pairCount, ih, List.countP_append, List.countP_cons]
    by_cases h : p a <;> simp [h]
    ring

theorem pairCount_map (p q : ℕ → Bool) (f : ℕ → ℕ) (xs : List ℕ) :
    pairCount p q (xs.map f) = pairCount (p ∘ f) (q ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [pairCount, ih]

def deeper (h d : ℕ) : Bool := decide (h < d)
def atLevel (h d : ℕ) : Bool := decide (d = h)

theorem score_partition (h : ℕ) (xs : List ℕ) :
    scoreSum h xs dfsScore =
      scoreSum h xs (dfsTruncScore h xs) + pairCount (deeper h) (atLevel h) xs := by
  rw [← pairCount_indices, scoreSum, scoreSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have htake : (xs.take i).length = i :=
    List.length_take_of_le (Nat.le_of_lt (mem_range.mp hi))
  have hq : (xs[i]?).any (atLevel h) = decide (xs[i]? = some h) := by
    cases xs[i]? <;> simp [atLevel]
  have hpart : ∀ ys : List ℕ,
      ((ys.filter (· ≤ h)).length + ys.countP (deeper h)) = ys.length := by
    intro ys
    induction ys with
    | nil => rfl
    | cons a as ih =>
      simp only [List.filter_cons, List.countP_cons, deeper, List.length_cons]
      by_cases h' : a ≤ h
      · simp [h', show ¬h < a by omega]
        omega
      · simp [h', show h < a by omega]
        omega
  simp only [hq, decide_eq_true_eq, dfsScore, dfsTruncScore]
  split
  · rw [hpart, htake]
  · simp

def depths (b : BinaryTree Unit) : List ℕ := preorderDepths (decode b)

def levelCount (h : ℕ) (b : BinaryTree Unit) : ℤ := (depths b).countP (atLevel h)
def aboveCount (h : ℕ) (b : BinaryTree Unit) : ℤ := (depths b).countP (deeper h)
def allCount (b : BinaryTree Unit) : ℤ := (depths b).length
def depthPairs (h : ℕ) (b : BinaryTree Unit) : ℤ := pairCount (deeper h) (atLevel h) (depths b)

theorem depths_node (l r : BinaryTree Unit) :
    depths (.node () l r) = 0 :: ((depths l).map Nat.succ ++ forestDepths (childrenOf r)) := rfl

theorem depths_root (r : BinaryTree Unit) : depths r = 0 :: forestDepths (childrenOf r) := rfl

theorem atLevel_shift (h : ℕ) : atLevel (h+1) ∘ Nat.succ = atLevel h := by
  funext d
  simp [atLevel]

theorem deeper_shift (h : ℕ) : deeper (h+1) ∘ Nat.succ = deeper h := by
  funext d
  simp [deeper]

@[simp] theorem levelCount_zero (b : BinaryTree Unit) : levelCount 0 b = 1 := by
  induction b using BinaryTree.unitRecOn with
  | base => rfl
  | ind l r il ir =>
    have hn : atLevel 0 ∘ Nat.succ = fun _ => false := by funext a; simp [atLevel]
    simp only [levelCount, depths_node, List.countP_cons, atLevel, decide_true, ite_true,
      List.countP_append, List.countP_map, hn, List.countP_false, Function.const_apply,
      zero_add] at *
    simpa [depths_root, List.countP_cons, atLevel] using ir

@[simp] theorem levelCount_nil (h : ℕ) : levelCount (h+1) .nil = 0 := by
  simp [levelCount, depths, decode, childrenOf, preorderDepths, forestDepths, atLevel]

theorem levelCount_node (h : ℕ) (l r : BinaryTree Unit) :
    levelCount (h+1) (.node () l r) = levelCount h l + levelCount (h+1) r := by
  unfold levelCount
  rw [depths_node, depths_root r]
  simp [atLevel_shift, atLevel]

@[simp] theorem aboveCount_nil (h : ℕ) : aboveCount h .nil = 0 := by
  simp [aboveCount, depths, decode, childrenOf, preorderDepths, forestDepths, deeper]

theorem aboveCount_node (h : ℕ) (l r : BinaryTree Unit) :
    aboveCount (h+1) (.node () l r) = aboveCount h l + aboveCount (h+1) r := by
  unfold aboveCount
  rw [depths_node, depths_root r]
  simp [deeper_shift, deeper]

theorem aboveCount_zero_node (l r : BinaryTree Unit) :
    aboveCount 0 (.node () l r) = allCount l + aboveCount 0 r := by
  have hn : deeper 0 ∘ Nat.succ = fun _ => true := by funext a; simp [deeper]
  unfold aboveCount allCount
  rw [depths_node, depths_root r]
  simp [hn, deeper]

@[simp] theorem allCount_nil : allCount .nil = 1 := rfl

theorem allCount_node (l r : BinaryTree Unit) :
    allCount (.node () l r) = allCount l + allCount r := by
  unfold allCount
  rw [depths_node, depths_root r]
  simp [add_assoc]

@[simp] theorem depthPairs_nil (h : ℕ) : depthPairs h .nil = 0 := by
  simp [depthPairs, depths, decode, childrenOf, preorderDepths, forestDepths, pairCount, deeper]

@[simp] theorem depthPairs_zero (b : BinaryTree Unit) : depthPairs 0 b = 0 := by
  induction b using BinaryTree.unitRecOn with
  | base => rfl
  | ind l r il ir =>
    have hn : atLevel 0 ∘ Nat.succ = fun _ => false := by funext a; simp [atLevel]
    have hfalse (xs : List ℕ) (p : ℕ → Bool) : pairCount p (fun _ => false) xs = 0 := by
      induction xs with
      | nil => rfl
      | cons a as ih => by_cases hp : p a <;> simp [pairCount, ih, hp]
    simp only [depthPairs, depths_node, pairCount, deeper, lt_self_iff_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, add_zero, pairCount_append, pairCount_map,
      hn, hfalse, zero_add]
    have hz : (forestDepths (childrenOf r)).countP (atLevel 0) = 0 := by
      have hr := levelCount_zero r
      rw [levelCount, depths_root r, List.countP_cons_of_pos (show atLevel 0 0 from rfl)] at hr
      omega
    simpa [depthPairs, depths_root r, pairCount, deeper, hz] using ir

theorem depthPairs_node (h : ℕ) (l r : BinaryTree Unit) :
    depthPairs (h+1) (.node () l r) =
      depthPairs h l + depthPairs (h+1) r + aboveCount h l * levelCount (h+1) r := by
  unfold depthPairs aboveCount levelCount
  rw [depths_node, depths_root r]
  simp [pairCount, pairCount_append, pairCount_map,
    deeper_shift, atLevel_shift, deeper, atLevel]

theorem total_difference (n h : ℕ) :
    (totalD n h : ℤ) - totalDTrunc n h =
      ∑ b ∈ BinaryTree.treesOfNumNodesEq n, depthPairs h b := by
  have ht : totalD n h = totalDTrunc n h +
      ∑ t ∈ trees n, pairCount (deeper h) (atLevel h) (preorderDepths t) := by
    unfold totalD totalDTrunc
    rw [← sum_add_distrib]
    exact sum_congr rfl fun t _ => score_partition h (preorderDepths t)
  rw [ht, Nat.cast_add, add_sub_cancel_left, Nat.cast_sum, trees, sum_map]
  rfl

#print axioms total_difference

end DMZ
```

### `DMZPolynomials.lean`

```lean
import DMZTrees
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset Polynomial
open scoped BigOperators

namespace DMZ

noncomputable section

abbrev ZPoly := Polynomial ℤ

def CoeffNonneg (p : ZPoly) : Prop := ∀ j, 0 ≤ p.coeff j

theorem CoeffNonneg.add {p q : ZPoly} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p + q) := fun j => by simpa using add_nonneg (hp j) (hq j)

theorem CoeffNonneg.mul {p q : ZPoly} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := by
  intro j
  rw [coeff_mul]
  exact sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

theorem nonneg_C {c : ℤ} (hc : 0 ≤ c) : CoeffNonneg (C c) := by
  intro j
  rw [coeff_C]
  split <;> simp_all

theorem nonneg_X_pow (d : ℕ) : CoeffNonneg ((X : ZPoly) ^ d) := by
  intro j
  rw [coeff_X_pow]
  split <;> decide

variable (E O : ℕ → ZPoly) (s : ℕ)

/-- Product of positive-sign blocks at consecutive indices. -/
def plusProduct : ℕ → ℕ → ZPoly
  | 0, _ => 1
  | d + 1, c => (E c + O c) * plusProduct d (c + s)

/-- Sum over cuts, omitting the cut block, with a sign change before the cut. -/
def cutPoly : ℕ → ℕ → ZPoly
  | 0, _ => 0
  | d + 1, c => plusProduct E O s d (c + s) + (E c - O c) * cutPoly d (c + s)

/-- The cut sum and the product minus any smaller block times the cut sum
are simultaneously coefficientwise nonnegative. -/
theorem cutPoly_nonneg_aux (hE : ∀ c, CoeffNonneg (E c)) (hO : ∀ c, CoeffNonneg (O c))
    (hmono : ∀ c c', c ≤ c' → CoeffNonneg (O c' - O c)) (d c : ℕ) :
    CoeffNonneg (cutPoly E O s d c) ∧
      ∀ q : ZPoly, CoeffNonneg q → CoeffNonneg (O c - q) →
        CoeffNonneg (plusProduct E O s d c - q * cutPoly E O s d c) := by
  induction d generalizing c with
  | zero => simp [cutPoly, plusProduct, CoeffNonneg, coeff_one, apply_ite]
  | succ d ih =>
    obtain ⟨hp, hr⟩ := ih (c + s)
    have hinc := hmono c (c + s) (Nat.le_add_right _ _)
    constructor
    · rw [cutPoly, show plusProduct E O s d (c+s) + (E c - O c) * cutPoly E O s d (c+s) =
          E c * cutPoly E O s d (c+s) +
            (plusProduct E O s d (c+s) - O c * cutPoly E O s d (c+s)) by ring]
      exact ((hE c).mul hp).add (hr _ (hO c) hinc)
    · intro q hq hc
      have hnext : CoeffNonneg (O (c+s) - q) := by
        rw [show O (c+s) - q = (O (c+s) - O c) + (O c - q) by ring]
        exact hinc.add hc
      rw [plusProduct, cutPoly, show
        (E c + O c) * plusProduct E O s d (c+s) -
          q * (plusProduct E O s d (c+s) + (E c - O c) * cutPoly E O s d (c+s)) =
        (E c + (O c - q)) * (plusProduct E O s d (c+s) - q * cutPoly E O s d (c+s)) +
          q * (O c + (O c - q)) * cutPoly E O s d (c+s) by ring]
      exact (((hE c).add hc).mul (hr _ hq hnext)).add ((hq.mul ((hO c).add hc)).mul hp)

def oddE (_ : ℕ) : ZPoly := X
def oddO (c : ℕ) : ZPoly := C (c : ℤ)
def evenE (c : ℕ) : ZPoly := X ^ 2 + C ((c : ℤ) * ((c : ℤ) + 1))
def evenO (c : ℕ) : ZPoly := C (2 * (c : ℤ) + 1) * X

def aPoly (d c : ℕ) : ZPoly := cutPoly oddE oddO 1 (d + 1) c
def bPoly (d c : ℕ) : ZPoly := cutPoly evenE evenO 2 (d + 1) c

theorem aPoly_nonneg (d c : ℕ) : CoeffNonneg (aPoly d c) := by
  apply (cutPoly_nonneg_aux oddE oddO 1 ?_ ?_ ?_ _ _).1
  · intro k
    simpa [oddE] using nonneg_X_pow 1
  · intro k
    exact nonneg_C (by omega)
  · intro i j hij
    unfold oddO
    rw [← map_sub]
    exact nonneg_C (by omega)

theorem bPoly_nonneg (d c : ℕ) : CoeffNonneg (bPoly d c) := by
  have hx : CoeffNonneg (X : ZPoly) := by simpa using nonneg_X_pow 1
  apply (cutPoly_nonneg_aux evenE evenO 2 ?_ ?_ ?_ _ _).1
  · intro k
    exact (nonneg_X_pow 2).add (nonneg_C (mul_nonneg (by omega) (by omega)))
  · intro k
    exact (nonneg_C (by omega)).mul hx
  · intro i j hij
    unfold evenO
    rw [← sub_mul, ← map_sub]
    exact (nonneg_C (by omega)).mul hx

theorem add_top_coeff {p q : ZPoly} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (h : p.coeff d + q.coeff d ≠ 0) :
    (p + q).natDegree = d ∧ (p + q).leadingCoeff = p.coeff d + q.coeff d := by
  have hu : (p + q).natDegree ≤ d :=
    (natDegree_add_le _ _).trans (max_le hp hq)
  have hd : d ≤ (p + q).natDegree := le_natDegree_of_ne_zero (by rwa [coeff_add])
  have he := le_antisymm hu hd
  exact ⟨he, by rw [← coeff_natDegree, he, coeff_add]⟩

theorem plusProduct_top {w : ℕ} (hp : ∀ c, (E c + O c).Monic ∧
    (E c + O c).natDegree = w) (d c : ℕ) :
    (plusProduct E O s d c).Monic ∧ (plusProduct E O s d c).natDegree = w * d := by
  induction d generalizing c with
  | zero => simp [plusProduct]
  | succ d ih =>
    obtain ⟨hm, hd⟩ := hp c
    obtain ⟨hm', hd'⟩ := ih (c + s)
    refine ⟨by rw [Monic, plusProduct, leadingCoeff_mul, hm.leadingCoeff, hm'.leadingCoeff, one_mul], ?_⟩
    rw [plusProduct, natDegree_mul hm.ne_zero hm'.ne_zero, hd, hd', Nat.mul_succ, Nat.add_comm]

theorem cutPoly_top {w : ℕ} (hp : ∀ c, (E c + O c).Monic ∧
    (E c + O c).natDegree = w) (hm : ∀ c, (E c - O c).Monic ∧
    (E c - O c).natDegree = w) (d c : ℕ) :
    (cutPoly E O s (d+1) c).natDegree = w * d ∧
      (cutPoly E O s (d+1) c).leadingCoeff = (d : ℤ) + 1 := by
  induction d generalizing c with
  | zero => simp [cutPoly, plusProduct]
  | succ d ih =>
    rw [cutPoly]
    obtain ⟨hmA, hA⟩ := plusProduct_top E O s hp (d+1) (c+s)
    obtain ⟨hmB, hB⟩ := hm c
    obtain ⟨hP, hlP⟩ := ih (c+s)
    have hNZ : cutPoly E O s (d+1) (c+s) ≠ 0 := by
      intro he
      rw [he, leadingCoeff_zero] at hlP
      omega
    have hD : ((E c - O c) * cutPoly E O s (d+1) (c+s)).natDegree = w * (d+1) := by
      rw [natDegree_mul hmB.ne_zero hNZ, hB, hP, Nat.mul_succ, Nat.add_comm]
    have hcA : (plusProduct E O s (d+1) (c+s)).coeff (w * (d+1)) = 1 := by
      rw [← hA, coeff_natDegree, hmA.leadingCoeff]
    have hcB : ((E c - O c) * cutPoly E O s (d+1) (c+s)).coeff (w * (d+1)) =
        (d : ℤ) + 1 := by
      rw [← hD, coeff_natDegree, leadingCoeff_mul, hmB.leadingCoeff, one_mul, hlP]
    obtain ⟨hd, hc⟩ := add_top_coeff hA.le hD.le (by rw [hcA, hcB]; omega)
    refine ⟨hd, ?_⟩
    rw [hc, hcA, hcB]
    omega

theorem odd_blocks (c : ℕ) :
    (oddE c + oddO c).Monic ∧ (oddE c + oddO c).natDegree = 1 ∧
    (oddE c - oddO c).Monic ∧ (oddE c - oddO c).natDegree = 1 := by
  simp only [oddE, oddO, ← map_neg, sub_eq_add_neg]
  have h (z : ℤ) : (X + C z).Monic ∧ (X + C z).natDegree = 1 := by
    obtain ⟨hd, hc⟩ := add_top_coeff (p := X) (q := C z) (d := 1)
      (by simp) (by simp) (by rw [coeff_C_succ]; simp)
    rw [coeff_C_succ, add_zero, coeff_X_one] at hc
    exact ⟨hc, hd⟩
  exact ⟨(h _).1, (h _).2, (h _).1, (h _).2⟩

theorem even_blocks (c : ℕ) :
    (evenE c + evenO c).Monic ∧ (evenE c + evenO c).natDegree = 2 ∧
    (evenE c - evenO c).Monic ∧ (evenE c - evenO c).natDegree = 2 := by
  have h (z t : ℤ) : (X ^ 2 + (C z + C t * X)).Monic ∧
      (X ^ 2 + (C z + C t * X)).natDegree = 2 := by
    have hb : (C z + C t * X).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp)
        ((natDegree_mul_le).trans (by simp)))
    have hz := coeff_eq_zero_of_natDegree_lt (p := C z + C t * X) (n := 2)
      (lt_of_le_of_lt hb (by decide))
    obtain ⟨hd, hc⟩ := add_top_coeff (p := X ^ 2) (q := C z + C t * X) (d := 2)
      (by simp) (hb.trans (by decide)) (by rw [hz, add_zero, coeff_X_pow_self]; decide)
    rw [hz, add_zero, coeff_X_pow_self] at hc
    exact ⟨hc, hd⟩
  simp only [evenE, evenO, sub_eq_add_neg, ← neg_mul, ← map_neg, add_assoc]
  exact ⟨(h _ _).1, (h _ _).2, (h _ _).1, (h _ _).2⟩

theorem aPoly_top (d c : ℕ) :
    (aPoly d c).natDegree = d ∧ (aPoly d c).leadingCoeff = (d : ℤ) + 1 := by
  simpa [aPoly] using cutPoly_top oddE oddO 1
    (fun c => ⟨(odd_blocks c).1, (odd_blocks c).2.1⟩) (fun c => (odd_blocks c).2.2) d c

theorem bPoly_top (d c : ℕ) :
    (bPoly d c).natDegree = 2*d ∧ (bPoly d c).leadingCoeff = (d : ℤ) + 1 :=
  cutPoly_top evenE evenO 2 (fun c => ⟨(even_blocks c).1, (even_blocks c).2.1⟩)
    (fun c => (even_blocks c).2.2) d c

#print axioms aPoly_nonneg
#print axioms bPoly_nonneg
#print axioms aPoly_top
#print axioms bPoly_top

end

end DMZ
```

### `DMZBinomial.lean`

```lean
import DMZPolynomials
import Mathlib.Tactic.LinearCombination

open Finset Polynomial
open scoped BigOperators

namespace DMZ

theorem chooseZ_neg (N : ℕ) {k : ℤ} (hk : k < 0) : chooseZ N k = 0 := by
  simp [chooseZ, hk]

@[simp] theorem chooseZ_nat (N k : ℕ) : chooseZ N (k : ℤ) = N.choose k := by
  simp [chooseZ]

theorem chooseZ_pascal (N : ℕ) (k : ℤ) :
    chooseZ (N+1) k = chooseZ N k + chooseZ N (k-1) := by
  by_cases h : k ≤ 0
  · rcases lt_or_eq_of_le h with h' | rfl
    · rw [chooseZ_neg _ h', chooseZ_neg _ h', chooseZ_neg _ (by omega), add_zero]
    · rw [chooseZ_neg N (k := 0 - 1) (by omega)]
      change chooseZ (N+1) ((0 : ℕ) : ℤ) = chooseZ N ((0 : ℕ) : ℤ) + 0
      simp [chooseZ]
  · have hk : k = ((k.toNat - 1 + 1 : ℕ) : ℤ) := by omega
    conv_lhs => rw [hk, chooseZ_nat]
    have hs : k - 1 = ((k.toNat - 1 : ℕ) : ℤ) := by omega
    conv_rhs => rw [hs, chooseZ_nat, hk, chooseZ_nat]
    -- Rewriting the naturalized positive index uses Pascal's rule.
    simp only [Int.toNat_natCast, Nat.add_sub_cancel] at *
    rw [Nat.choose_succ_succ', add_comm, Int.natCast_add]

theorem chooseZ_prev (N : ℕ) (k : ℤ) (hk : k ≤ (N : ℤ)) :
    chooseZ N (k-1) * ((N : ℤ) - k + 1) = chooseZ N k * k := by
  by_cases h : k ≤ 0
  · rw [chooseZ_neg _ (by omega), zero_mul]
    rcases lt_or_eq_of_le h with h' | rfl
    · rw [chooseZ_neg _ h', zero_mul]
    · rw [mul_zero]
  · let j := k.toNat - 1
    have h1 : k = ((j+1 : ℕ) : ℤ) := by dsimp [j]; omega
    have h2 : k-1 = (j : ℤ) := by omega
    have h3 : (N : ℤ)-k+1 = ((N-j : ℕ) : ℤ) := by omega
    conv_lhs => rw [h2, h3, chooseZ_nat]
    conv_rhs => rw [h1, chooseZ_nat]
    exact_mod_cast (Nat.choose_succ_right_eq N j).symm

/-- Sum over the initial `d` blocks, starting at `c` and advancing by `s`. -/
def blockSum (B : ℕ → ℤ) (s : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | d+1, c => B c + blockSum B s d (c+s)

theorem blockSum_range (B : ℕ → ℤ) (s d c : ℕ) :
    blockSum B s d c = ∑ i ∈ range d, B (c+s*i) := by
  induction d generalizing c with
  | zero => simp [blockSum]
  | succ d ih =>
    rw [blockSum, sum_range_succ', ih]
    simp only [mul_zero, add_zero]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [Nat.mul_succ, add_right_comm, add_assoc]

theorem normalizeBlocks (E O : ℕ → ZPoly) (s : ℕ) (x : ℤ) (B : ℕ → ℤ)
    (h : ∀ c, B (c+s) * (E (c+s) + O (c+s)).eval x = B c * (E c - O c).eval x)
    (d c : ℕ) :
    blockSum B s (d+1) c * (plusProduct E O s d (c+s)).eval x =
      B c * (cutPoly E O s (d+1) c).eval x := by
  induction d generalizing c with
  | zero => simp [blockSum, plusProduct, cutPoly]
  | succ d ih =>
    rw [blockSum, cutPoly, eval_add, eval_mul, add_mul, mul_add]
    congr 1
    calc
      blockSum B s (d+1) (c+s) * (plusProduct E O s (d+1) (c+s)).eval x =
        (blockSum B s (d+1) (c+s) * (plusProduct E O s d (c+s+s)).eval x) *
          (E (c+s) + O (c+s)).eval x := by rw [plusProduct, eval_mul]; ring
      _ = _ := by rw [ih]; linear_combination (cutPoly E O s (d+1) (c+s)).eval x * h c

theorem rising_first (n d : ℕ) :
    rising n (d+1) = (n : ℤ) * rising (n+1) d := by
  unfold rising
  rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
  push_cast
  rfl

theorem odd_den (n d c : ℕ) :
    (plusProduct oddE oddO 1 d c).eval (n : ℤ) = rising (n+c) d := by
  induction d generalizing c with
  | zero => simp [plusProduct, rising]
  | succ d ih =>
    rw [plusProduct, eval_mul, ih, rising_first]
    simp [oddE, oddO, Nat.add_assoc]

theorem even_den (n d c : ℕ) :
    (plusProduct evenE evenO 2 d c).eval (n : ℤ) = rising (n+c) (2*d) := by
  induction d generalizing c with
  | zero => simp [plusProduct, rising]
  | succ d ih =>
    rw [plusProduct, eval_mul, ih, Nat.mul_succ, rising_first, rising_first]
    simp only [evenE, evenO, eval_add, eval_X_pow, eval_C, eval_mul, eval_X,
      Nat.cast_add, Nat.cast_one]
    rw [show n + (c+2) = n+c+1+1 by omega]
    ring

theorem odd_normalize (n d c : ℕ) :
    (∑ i ∈ range (d+1), chooseZ (2*n) ((n : ℤ)-(c+i : ℕ))) *
      rising (n+c+1) d = (aPoly d c).eval (n : ℤ) * chooseZ (2*n) ((n : ℤ)-c) := by
  let B (k : ℕ) := chooseZ (2*n) ((n : ℤ)-k)
  have h k : B (k+1) * (oddE (k+1) + oddO (k+1)).eval (n : ℤ) =
      B k * (oddE k - oddO k).eval (n : ℤ) := by
    have hp := chooseZ_prev (2*n) ((n : ℤ)-k) (by push_cast; omega)
    simp only [B, oddE, oddO, eval_add, eval_sub, eval_X, eval_C, Nat.cast_add,
      Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at *
    rw [show (n : ℤ) - ((k : ℤ) + 1) = n - k - 1 by ring]
    linear_combination hp
  have hp := normalizeBlocks oddE oddO 1 (n : ℤ) B h d c
  rw [blockSum_range, odd_den, ← aPoly, mul_comm (B c)] at hp
  simpa [B, Nat.add_assoc] using hp

theorem even_normalize (n d c : ℕ) :
    (∑ i ∈ range (d+1), chooseZ (2*n+1) ((n : ℤ)-(c+2*i : ℕ))) *
      rising (n+c+2) (2*d) = (bPoly d c).eval (n : ℤ) * chooseZ (2*n+1) ((n : ℤ)-c) := by
  let N := 2*n+1
  let B (k : ℕ) := chooseZ N ((n : ℤ)-k)
  have h k : B (k+2) * (evenE (k+2) + evenO (k+2)).eval (n : ℤ) =
      B k * (evenE k - evenO k).eval (n : ℤ) := by
    have h0 : B (k+1) * ((n : ℤ)+k+2) = B k * ((n : ℤ)-k) := by
      have hp := chooseZ_prev N ((n : ℤ)-k) (by dsimp [N]; omega)
      simp only [B, N, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at *
      rw [show (n : ℤ) - ((k : ℤ) + 1) = n - k - 1 by ring]
      linear_combination hp
    have h1 : B (k+2) * ((n : ℤ)+k+3) = B (k+1) * ((n : ℤ)-k-1) := by
      have hp := chooseZ_prev N ((n : ℤ)-k-1) (by dsimp [N]; omega)
      simp only [B, N, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at *
      rw [show (n : ℤ) - ((k : ℤ) + 2) = n - k - 1 - 1 by ring]
      rw [show (n : ℤ) - ((k : ℤ) + 1) = n - k - 1 by ring]
      linear_combination hp
    simp only [evenE, evenO, eval_add, eval_X_pow, eval_C, eval_mul, eval_sub, eval_X,
      Nat.cast_add, Nat.cast_ofNat]
    linear_combination ((n : ℤ)+k+2) * h1 + ((n : ℤ)-k-1) * h0
  have hp := normalizeBlocks evenE evenO 2 (n : ℤ) B h d c
  rw [blockSum_range, even_den, ← bPoly, mul_comm (B c)] at hp
  simpa [B, N, Nat.add_assoc] using hp

#print axioms odd_normalize
#print axioms even_normalize

end DMZ
```

### `DMZSeries.lean`

```lean
import DMZScores
import DMZBinomial
import Mathlib.RingTheory.PowerSeries.Basic

open Finset
open scoped BigOperators PowerSeries

namespace DMZ

noncomputable section

abbrev Series := PowerSeries ℤ
abbrev BT := BinaryTree Unit
local notation "leaf" => BinaryTree.nil
local notation l " ◇ " r => BinaryTree.node () l r
local notation "z" => (PowerSeries.X : Series)

def series (f : BT → ℤ) : Series :=
  PowerSeries.mk fun n => ∑ b ∈ BinaryTree.treesOfNumNodesEq n, f b

@[simp] theorem coeff_series (f : BT → ℤ) (n : ℕ) :
    PowerSeries.coeff n (series f) = ∑ b ∈ BinaryTree.treesOfNumNodesEq n, f b :=
  PowerSeries.coeff_mk _ _

/-- First-child split of the sum over ordered trees with `n+1` edges. -/
theorem sum_first_child (f : BT → ℤ) (n : ℕ) :
    (∑ b ∈ BinaryTree.treesOfNumNodesEq (n+1), f b) =
      ∑ ij ∈ antidiagonal n,
        ∑ l ∈ BinaryTree.treesOfNumNodesEq ij.1,
          ∑ r ∈ BinaryTree.treesOfNumNodesEq ij.2, f (l ◇ r) := by
  classical
  rw [BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
  · apply sum_congr rfl
    intro ij _
    rw [sum_map, sum_product]
    rfl
  · intro i hi j hj hne
    refine disjoint_left.mpr fun b hb hb' => hne ?_
    simp only [BinaryTree.pairwiseNode, mem_map, mem_product,
      BinaryTree.mem_treesOfNumNodesEq] at hb hb'
    obtain ⟨⟨l, r⟩, ⟨hl, hr⟩, rfl⟩ := hb
    obtain ⟨⟨l', r'⟩, ⟨hl', hr'⟩, he⟩ := hb'
    cases he
    exact Prod.ext (hl.symm.trans hl') (hr.symm.trans hr')

def treeSeries : Series := series (fun _ => 1)
def stepSeries : Series := z * treeSeries ^ 2
def levelSeries (h : ℕ) : Series := series (levelCount h)
def aboveSeries (h : ℕ) : Series := series (aboveCount h)
def pairSeries (h : ℕ) : Series := series (depthPairs h)
def vertexSeries : Series := series allCount

theorem series_split (f g h a b : BT → ℤ)
    (hf : ∀ l r : BT, f (l ◇ r) = g l + h r + a l * b r) :
    series f = PowerSeries.C (f leaf) +
      z * (series g * treeSeries + treeSeries * series h + series a * series b) := by
  ext n
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [map_add, PowerSeries.coeff_succ_X_mul]
    simp only [map_add, PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, zero_add,
      PowerSeries.coeff_mul, coeff_series, treeSeries]
    rw [sum_first_child, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro ij _
    simp only [hf, sum_add_distrib, sum_mul_sum, mul_one, one_mul]

@[simp] theorem series_zero : series (fun _ => 0) = 0 := by
  ext n
  simp

theorem treeSeries_eq : treeSeries = 1 + z * treeSeries ^ 2 := by
  have h := series_split (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (by simp)
  simpa [treeSeries, sq] using h

theorem solve_right (F G W : Series)
    (h : F = z * (G * treeSeries + treeSeries * F + W)) :
    F = stepSeries * G + z * treeSeries * W := by
  unfold stepSeries
  linear_combination treeSeries * h - F * treeSeries_eq

theorem levelSeries_zero : levelSeries 0 = treeSeries := by
  simp [levelSeries, treeSeries, show levelCount 0 = fun _ => 1 from funext levelCount_zero]

theorem levelSeries_succ (h : ℕ) : levelSeries (h+1) = stepSeries * levelSeries h := by
  have he := series_split (levelCount (h+1)) (levelCount h) (levelCount (h+1))
    (fun _ => 0) (fun _ => 0) (by intro l r; rw [levelCount_node, zero_mul, add_zero])
  simpa using solve_right (levelSeries (h+1)) (levelSeries h) 0
    (by simpa [levelSeries] using he)

theorem levelSeries_eq (h : ℕ) : levelSeries h = stepSeries ^ h * treeSeries := by
  induction h with
  | zero => simp [levelSeries_zero]
  | succ h ih => rw [levelSeries_succ, ih, pow_succ']; ring

theorem aboveSeries_zero : aboveSeries 0 = stepSeries * vertexSeries := by
  have he := series_split (aboveCount 0) allCount (aboveCount 0)
    (fun _ => 0) (fun _ => 0) (by intro l r; rw [aboveCount_zero_node, zero_mul, add_zero])
  simpa using solve_right (aboveSeries 0) vertexSeries 0
    (by simpa [aboveSeries, vertexSeries] using he)

theorem aboveSeries_succ (h : ℕ) : aboveSeries (h+1) = stepSeries * aboveSeries h := by
  have he := series_split (aboveCount (h+1)) (aboveCount h) (aboveCount (h+1))
    (fun _ => 0) (fun _ => 0) (by intro l r; rw [aboveCount_node, zero_mul, add_zero])
  simpa using solve_right (aboveSeries (h+1)) (aboveSeries h) 0
    (by simpa [aboveSeries] using he)

theorem aboveSeries_eq (h : ℕ) : aboveSeries h = stepSeries ^ (h+1) * vertexSeries := by
  induction h with
  | zero => simpa using aboveSeries_zero
  | succ h ih => rw [aboveSeries_succ, ih, pow_succ']; ring

theorem vertexSeries_eq : vertexSeries = 1 + z * (vertexSeries * treeSeries +
    treeSeries * vertexSeries) := by
  have he := series_split allCount allCount allCount (fun _ => 0) (fun _ => 0)
    (by intro l r; rw [allCount_node, zero_mul, add_zero])
  simpa [vertexSeries] using he

theorem pairSeries_zero : pairSeries 0 = 0 := by
  simp [pairSeries, show depthPairs 0 = fun _ => 0 from funext depthPairs_zero]

def colSeries (j : ℕ) : Series := stepSeries ^ j * vertexSeries

theorem pairSeries_succ (h : ℕ) :
    pairSeries (h+1) = stepSeries * pairSeries h + colSeries (2*h+3) := by
  have he := series_split (depthPairs (h+1)) (depthPairs h) (depthPairs (h+1))
    (aboveCount h) (levelCount (h+1)) (depthPairs_node h)
  rw [show pairSeries (h+1) = stepSeries * pairSeries h +
      z * treeSeries * (aboveSeries h * levelSeries (h+1)) from
    solve_right _ _ _ (by simpa [pairSeries, aboveSeries, levelSeries] using he)]
  rw [aboveSeries_eq, levelSeries_eq, colSeries, show 2*h+3 = (h+1)+(h+1)+1 by omega,
    pow_succ, pow_add, stepSeries]
  ring

theorem pairSeries_eq (h : ℕ) :
    pairSeries h = ∑ i ∈ range h, colSeries (h+2+i) := by
  induction h with
  | zero => simp [pairSeries_zero]
  | succ h ih =>
    rw [pairSeries_succ, ih, sum_range_succ, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro i _
      rw [colSeries, colSeries, show h+1+2+i = (h+2+i)+1 by omega, pow_succ']
      ring
    · congr 1
      omega

theorem colSeries_center : colSeries 0 = 1 + z * (2 * (colSeries 0 + colSeries 1)) := by
  simp only [colSeries, pow_zero, pow_one, one_mul]
  have h : treeSeries = 1 + stepSeries := treeSeries_eq
  rw [← one_add_mul, ← h]
  linear_combination vertexSeries_eq

theorem colSeries_rec (j : ℕ) :
    colSeries (j+1) = z * (colSeries j + 2 * colSeries (j+1) + colSeries (j+2)) := by
  have h : stepSeries = z * (1 + stepSeries) ^ 2 := by
    have h' : treeSeries = 1 + stepSeries := treeSeries_eq
    rw [← h']
    rfl
  simp only [colSeries, pow_succ]
  linear_combination (stepSeries^j * vertexSeries) * h

def binom (n j : ℕ) : ℤ := chooseZ (2*n) ((n : ℤ)-j)

theorem binom_zero (j : ℕ) : binom 0 j = if j = 0 then 1 else 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [binom, chooseZ_neg _ (by omega)]; simp

theorem binom_rec (n j : ℕ) :
    binom (n+1) (j+1) = binom n j + 2 * binom n (j+1) + binom n (j+2) := by
  simp only [binom, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show 2*(n+1) = (2*n+1)+1 by omega,
    show (n : ℤ)+1-((j : ℤ)+1) = n-j by ring,
    chooseZ_pascal, chooseZ_pascal (2*n), chooseZ_pascal (2*n)]
  rw [show (n : ℤ)-((j : ℤ)+1) = n-j-1 by ring,
    show (n : ℤ)-((j : ℤ)+2) = n-j-1-1 by ring]
  ring

theorem binom_center (n : ℕ) : binom (n+1) 0 = 2 * (binom n 0 + binom n 1) := by
  have hs : chooseZ (2*n) ((n : ℤ)+1) = chooseZ (2*n) ((n : ℤ)-1) := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [show ((n+1 : ℕ) : ℤ)+1 = ((n+2 : ℕ) : ℤ) by omega,
        show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega, chooseZ_nat, chooseZ_nat]
      have h := Nat.choose_symm (n := 2 * (n+1)) (k := n+2) (by omega)
      rw [show 2*(n+1)-(n+2) = n by omega] at h
      exact congrArg (fun a : ℕ => (a : ℤ)) h.symm
  simp only [binom, Nat.cast_add, Nat.cast_zero, Nat.cast_one, sub_zero]
  rw [show 2*(n+1) = (2*n+1)+1 by omega, chooseZ_pascal,
    chooseZ_pascal (2*n), chooseZ_pascal (2*n)]
  rw [show (n : ℤ)+1-1 = n by ring, hs]
  ring

theorem coeff_colSeries (n j : ℕ) : PowerSeries.coeff n (colSeries j) = binom n j := by
  induction n generalizing j with
  | zero =>
    rw [binom_zero]
    cases j with
    | zero => rw [colSeries_center]; simp
    | succ j => rw [colSeries_rec]; simp
  | succ n ih =>
    cases j with
    | zero =>
      rw [colSeries_center, binom_center, map_add, PowerSeries.coeff_succ_X_mul]
      simp [show (2 : Series) * (colSeries 0 + colSeries 1) =
        (colSeries 0 + colSeries 1) + (colSeries 0 + colSeries 1) by ring, ih,
        PowerSeries.coeff_one, two_mul]
    | succ j =>
      rw [colSeries_rec, binom_rec, PowerSeries.coeff_succ_X_mul]
      simp [two_mul, ih]

theorem depth_difference_binomial (n h : ℕ) :
    (totalD n h : ℤ) - totalDTrunc n h = ∑ i ∈ range h, binom n (h+2+i) := by
  rw [total_difference, ← coeff_series (depthPairs h) n]
  change PowerSeries.coeff n (pairSeries h) = _
  simp [pairSeries_eq, coeff_colSeries]

#print axioms depth_difference_binomial

end

end DMZ
```

### `DMZConjecture.lean`

```lean
import DMZSeries
import Mathlib.Data.Rat.Cast.Order

open Finset Polynomial
open scoped BigOperators

namespace DMZ

theorem even_pair_sum (n c d : ℕ) :
    (∑ i ∈ range (2*d), binom n (c+i)) =
      ∑ i ∈ range d, chooseZ (2*n+1) ((n : ℤ)-(c+2*i : ℕ)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, show 2*d+2 = (2*d+1)+1 by omega,
      sum_range_succ, sum_range_succ, sum_range_succ, ih, add_assoc]
    congr 1
    rw [chooseZ_pascal]
    simp only [binom, Nat.cast_add, Nat.cast_one]
    rw [show (n : ℤ) - ((c : ℤ) + (((2*d : ℕ) : ℤ) + 1)) =
      n - ((c : ℤ) + ((2*d : ℕ) : ℤ)) - 1 by ring]

theorem rising_clear (A B K : ℤ) (m d : ℕ) (hm : 0 < m) :
    (A : ℚ) = (B : ℚ) / (rising m d : ℚ) * (K : ℚ) ↔
      A * rising m d = B * K := by
  have h : (0 : ℚ) < (rising m d : ℚ) := by exact_mod_cast rising_pos hm d
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt h)]
  norm_cast

/-- Dimitrov–Minchev–Zhuang, arXiv:2404.05664v1, Conjecture 7.6.
The denominator-cleared integer version. -/
theorem dmz_conj_7_6 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ a b : Polynomial ℤ,
      a.natDegree = 2 * ℓ - 2 ∧ b.natDegree = 2 * ℓ - 2 ∧
      a.leadingCoeff = 2 * (ℓ : ℤ) - 1 ∧ b.leadingCoeff = (ℓ : ℤ) ∧
      (∀ j, 0 ≤ a.coeff j ∧ 0 ≤ b.coeff j) ∧
      ∀ n : ℕ, ℓ ≤ n →
        ((totalD n (2 * ℓ - 1) : ℤ) - totalDTrunc n (2 * ℓ - 1)) *
          rising (n + 2 * ℓ + 2) (2 * ℓ - 2) =
          a.eval (n : ℤ) * chooseZ (2 * n) ((n : ℤ) - 2 * ℓ - 1) ∧
        ((totalD n (2 * ℓ) : ℤ) - totalDTrunc n (2 * ℓ)) *
          rising (n + 2 * ℓ + 4) (2 * ℓ - 2) =
          b.eval (n : ℤ) * chooseZ (2 * n + 1) ((n : ℤ) - 2 * ℓ - 2) := by
  let d := ℓ-1
  let c := 2*ℓ+1
  let c' := 2*ℓ+2
  obtain ⟨haD, haL⟩ := aPoly_top (2*d) c
  obtain ⟨hbD, hbL⟩ := bPoly_top d c'
  refine ⟨aPoly (2*d) c, bPoly d c', by dsimp [d] at *; omega,
    by dsimp [d] at *; omega, by rw [haL]; dsimp [d]; omega,
    by rw [hbL]; dsimp [d]; omega,
    fun j => ⟨aPoly_nonneg _ _ j, bPoly_nonneg _ _ j⟩, fun n _ => ⟨?_, ?_⟩⟩
  · have hc : 2*ℓ-1+2 = c := by dsimp [c]; omega
    have hd : 2*ℓ-1 = 2*d+1 := by dsimp [d]; omega
    have hD : rising (n + 2*ℓ+2) (2*ℓ-2) = rising (n+c+1) (2*d) := by
      congr 1; dsimp [c, d]; omega
    have hK : (n : ℤ) - 2*ℓ - 1 = (n : ℤ)-c := by dsimp [c]; omega
    rw [depth_difference_binomial, hc, hd, hD, hK]
    exact odd_normalize n (2*d) c
  · have hd : 2*ℓ = 2*(d+1) := by dsimp [d]; omega
    have hD : rising (n + 2*ℓ+4) (2*ℓ-2) = rising (n+c'+2) (2*d) := by
      congr 1; dsimp [c', d]; omega
    have hK : (n : ℤ) - 2*ℓ - 2 = (n : ℤ)-c' := by dsimp [c']; omega
    rw [depth_difference_binomial, show 2*ℓ+2 = c' from rfl,
      show range (2*ℓ) = range (2*(d+1)) by rw [hd], even_pair_sum, hD, hK]
    exact even_normalize n d c'

theorem dmz_conj_7_6_div (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ a b : Polynomial ℤ,
      a.natDegree = 2 * ℓ - 2 ∧ b.natDegree = 2 * ℓ - 2 ∧
      a.leadingCoeff = 2 * (ℓ : ℤ) - 1 ∧ b.leadingCoeff = (ℓ : ℤ) ∧
      (∀ j, 0 ≤ a.coeff j ∧ 0 ≤ b.coeff j) ∧
      ∀ n : ℕ, ℓ ≤ n →
        (totalD n (2 * ℓ - 1) : ℚ) - totalDTrunc n (2 * ℓ - 1) =
          Int.cast (a.eval (n : ℤ)) / (rising (n + 2 * ℓ + 2) (2 * ℓ - 2) : ℚ) *
            (chooseZ (2 * n) ((n : ℤ) - 2 * ℓ - 1) : ℚ) ∧
        (totalD n (2 * ℓ) : ℚ) - totalDTrunc n (2 * ℓ) =
          Int.cast (b.eval (n : ℤ)) / (rising (n + 2 * ℓ + 4) (2 * ℓ - 2) : ℚ) *
            (chooseZ (2 * n + 1) ((n : ℤ) - 2 * ℓ - 2) : ℚ) := by
  obtain ⟨a, b, haD, hbD, haL, hbL, hpos, h⟩ := dmz_conj_7_6 ℓ hℓ
  refine ⟨a, b, haD, hbD, haL, hbL, hpos, fun n hn => ⟨?_, ?_⟩⟩
  · exact_mod_cast (rising_clear _ _ _ _ _ (by omega)).2 (h n hn).1
  · exact_mod_cast (rising_clear _ _ _ _ _ (by omega)).2 (h n hn).2

theorem nonzero_depth_differences :
    (totalD 3 1 : ℤ) - totalDTrunc 3 1 = 1 ∧
    (totalD 4 2 : ℤ) - totalDTrunc 4 2 = 1 := by
  rw [depth_difference_binomial, depth_difference_binomial]
  decide

/-- The polynomial in the third row of Table 3, with its quadratic coefficient corrected. -/
theorem table3_b3 :
    bPoly 2 8 = 3 * X^4 + 16 * X^3 + 1133 * X^2 + 1792 * X + 36312 := by
  norm_num [bPoly, cutPoly, plusProduct, evenE, evenO]
  ring

#check dmz_conj_7_6
#check dmz_conj_7_6_div
#print axioms dmz_conj_7_6
#print axioms dmz_conj_7_6_div
#print axioms nonzero_depth_differences
#print axioms rising_clear
#print axioms table3_b3

end DMZ
```

