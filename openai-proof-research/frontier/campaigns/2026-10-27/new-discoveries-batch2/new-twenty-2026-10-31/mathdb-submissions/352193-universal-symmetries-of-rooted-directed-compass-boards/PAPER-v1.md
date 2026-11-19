# Universal symmetries of directed compass boards
2026-11-15. Implementation certificate for MathDB 352193, source-interpreted as Ary Shaviv, *Board games, random boards and long boards*, arXiv:2110.05416v1 (11 October 2021), Definition 2, Definition 11, Section 5.1, Conjecture 15. No acceptance or novelty certification is claimed.

Fix an odd n≥3, write n=2k+1, k≥1, and m=n−1. Positions are pairs (i,j) with 0≤i,j≤m, increasing south and east. Directions are N,NE,E,SE,S,SW,W,NW. A board assigns an arbitrary direction to every position. Its graph has every position as a vertex and every positive integral step along its assigned ray as a directed edge, including outgoing edges at the center. The distinguished roots are s=(0,0) and c=(k,k). Graph isomorphisms must fix each root. For arbitrary permutations σ of positions and τ of directions, put S(A)(v)=τ(A(σ(v))). The universal hypothesis is that for every A there exists a rooted graph isomorphism from A to S(A); the isomorphism may depend on A.

**Theorem.** Such S are exactly identity and physical main-diagonal reflection R(A)(i,j)=r(A(j,i)), where r swaps N/W, E/S, NE/SW and fixes SE,NW. In fact the representing pair (σ,τ) is respectively (Id,Id) or (transpose,r), and both possibilities occur.

**Proof.** Let L_v(d) be the number of vertices strictly ahead along ray d, and E(A)=Σ_v L_v(A(v)). Every arc has exactly one source, so E is the complete arc count and is invariant under every graph isomorphism. Beginning-root outdegree is invariant as well. These invariants do not identify σ with the vertex map.

First separate directions without using diagonal sum formulas. All four cardinal totals T(d)=Σ_v L_v(d) are equal. Indeed L_N=i, L_S=m−i, L_W=j, L_E=m−j; reversing the row interchanges N/S totals, and swapping coordinates interchanges N/W and E/S totals. For NE or NW, project the target of each diagonal ray to the same row on the source column. This injects its ray targets into those of N. The step length is determined by the row difference, so projection is injective. For SE or SW use S instead. At a corner the relevant cardinal ray is nonempty while the diagonal ray is empty: use bottom-right for NE, bottom-left for NW, top-right for SE, top-left for SW. Thus every diagonal total is strictly below the common cardinal total. This proof works for every k≥1, including k=1. A constant board d transforms to the constant board τ(d); consequently T(d)=T(τ(d)). Strict separation implies that τ preserves the cardinal subset in both directions.

Now independently vary the input at σ(v), between any two directions d,e. Bijectivity of σ means that only output v varies. Subtract the two invariant arc-count equations in the integers:
L_v(τ(d))−L_v(τ(e))=L_σ(v)(d)−L_σ(v)(e).
Hence there is an integer b_v independent of d with
L_v(τ(d))=L_σ(v)(d)+b_v.
Since L_N+L_S=m=L_E+L_W everywhere, cancellation gives
L_v(τ(N))+L_v(τ(S))=L_v(τ(E))+L_v(τ(W))
at every v. If τ(N),τ(S) were adjacent cardinals, take the corner where both point outwards. Their lengths are zero, and the two complementary cardinal lengths are m each, contradicting m>0. Thus opposite cardinal pairs are preserved.

The beginning-root invariant gives L_s(A(s))=L_s(τ(A(σ(s)))) for every A. If σ(s)≠s, vary A(s) between N and E while keeping A(σ(s)) fixed; the two sides cannot remain equal, since these lengths are 0 and m. Thus σ(s)=s. Constant-board root invariance gives L_s(d)=L_s(τ(d)). The inward cardinal set {E,S} is therefore preserved, as is its outward complement {N,W}. Together with opposite preservation this gives exactly two cardinal actions: τ fixes N,S,W, or τ(N)=W, τ(S)=E, τ(W)=N. The Lean proof closes this same finite compass calculation using cardinal preservation, injectivity, constant-board root equations and opposite balance at the upper-right corner. It does not enumerate board sizes.

Physical reflection is a rooted graph isomorphism: transpose maps a positive ray step to the corresponding reflected ray step, is bijective, and fixes both s and c. Normalize the second cardinal case by composing R after S. With the pullback convention the normalized permutations are σ'=σ∘transpose and τ'=r∘τ. The normalized map remains universal and fixes N,S,W.

For this normalized map, add the local equations for N,S: m=m+2b_v, so b_v=0 in the integers for every vertex. The N and W equations now recover the row and column of σ(v), proving σ=Id. Thus L_v(τ(d))=L_v(d) everywhere. The eight ray-length profiles are distinct: at appropriate corners their zero/positive patterns separate every pair. Therefore τ=Id. Undoing reflection proves the two global alternatives. Identity and reflection have explicit rooted isomorphisms, proving sufficiency.

To pass to the source group of board permutations, the product action is a bijection: its inverse uses σ⁻¹ and τ⁻¹. The representation is faithful. Constant boards recover τ; after cancelling τ, a board distinguishing two candidate input positions recovers σ. Reflection differs from identity already on the constant north board. The source permutation set therefore equals {Id,R}. The odd-size bridge covers every odd n≥3. ∎

The zero-based coordinate translation is the bijection (a,b)↦(a−1,b−1) from the source's one-based grid; it preserves all signed step equations and takes the two named roots to s,c. The implementation uses this coordinate model directly rather than formalizing a second one-based graph structure.

## Certificate and limitations
Production dependency order: Board, Profiles, Reflection, Cardinals, Rigidity, Corners, Normalized, Separation, TotalSeparation, RootedCases, Endpoint, Action, AllSizes. The first eight supplied paid modules include Audit; the scientific dependency order above omits that diagnostic module. New scientific modules were compiled and separately checked with the pinned Lean kernel checker. ExpandedAudit covers all 117 declared objects and prints expanded definitions and source endpoints. Only propext, Classical.choice and Quot.sound occur transitively. Specific imports only; no added axioms, sorry, unsafe, native decision procedure, external oracle or finite-size extrapolation.

The source PDF pages 3,14,21 were extracted, rendered and personally inspected in this lane. Other PDF pages and the journal-final body were not newly read. The adopted independent ordinary correctness/source-v1 and bounded contribution/prior assessments remain scoped inherited evidence. This implementation is not an independent acceptance review or fresh extracted acceptance replay. Historical and new process defects remain UNWAIVED; see the integrated handoff and inventory. No count or credit changes.

## Complete byte-extractable Lean appendix
The separate APPENDIX-v1.json is a lossless UTF-8 extraction container. These fenced blocks reproduce every supplied and new module.

### Board.lean
```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Ring.Parity

/- Source: Shaviv arXiv:2110.05416v1, Definitions 2,11 and §5.1.
No gameplay stopping rule is imposed on the graph. -/
namespace BoardV1
open scoped BigOperators
abbrev Pos (n : ℕ) := Fin n × Fin n
abbrev Dir := Fin 8
abbrev Board (n : ℕ) := Pos n → Dir

def row (d : Dir) : ℤ :=
  match d.val with
  | 0 => -1 | 1 => -1 | 2 => 0 | 3 => 1
  | 4 => 1 | 5 => 1 | 6 => 0 | _ => -1

def col (d : Dir) : ℤ :=
  match d.val with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1
  | 4 => 0 | 5 => -1 | 6 => -1 | _ => -1

def Ray {n : ℕ} (v w : Pos n) (d : Dir) : Prop :=
  ∃ t : ℕ, 0 < t ∧
    (w.1.val : ℤ) = v.1.val + (t : ℤ) * row d ∧
    (w.2.val : ℤ) = v.2.val + (t : ℤ) * col d

def Edge {n : ℕ} (A : Board n) (v w : Pos n) : Prop := Ray v w (A v)

def Transform {n : ℕ} (σ : Equiv.Perm (Pos n)) (τ : Equiv.Perm Dir)
    (A : Board n) : Board n := fun v => τ (A (σ v))

def start (k : ℕ) : Pos (2*k+1) := (⟨0, by omega⟩, ⟨0, by omega⟩)
def center (k : ℕ) : Pos (2*k+1) := (⟨k, by omega⟩, ⟨k, by omega⟩)

structure RootedIso {k : ℕ} (A B : Board (2*k+1)) where
  vertex : Equiv.Perm (Pos (2*k+1))
  beginning : vertex (start k) = start k
  ending : vertex (center k) = center k
  edge_iff : ∀ v w, Edge A v w ↔ Edge B (vertex v) (vertex w)

def Universal {k : ℕ} (σ : Equiv.Perm (Pos (2*k+1))) (τ : Equiv.Perm Dir) : Prop :=
  ∀ A, Nonempty (RootedIso A (Transform σ τ A))

noncomputable def L {n : ℕ} (v : Pos n) (d : Dir) : ℤ := by
  classical
  exact ∑ w : Pos n, if Ray v w d then 1 else 0
noncomputable def total {n : ℕ} (A : Board n) : ℤ := ∑ v, L v (A v)

theorem odd_size_bridge (n : ℕ) :
    (Odd n ∧ 3 ≤ n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2*k+1 := by
  constructor
  · rintro ⟨⟨k, hk⟩, hn⟩
    exact ⟨k, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, by omega⟩, by omega⟩

theorem outdegree_iso {k : ℕ} {A B : Board (2*k+1)}
    (f : RootedIso A B) (v : Pos (2*k+1)) :
    L v (A v) = L (f.vertex v) (B (f.vertex v)) := by
  classical
  unfold L
  apply Fintype.sum_equiv f.vertex
  intro w
  have h := f.edge_iff v w
  unfold Edge at h
  rw [h]

theorem total_iso {k : ℕ} {A B : Board (2*k+1)} (f : RootedIso A B) :
    total A = total B := by
  classical
  unfold total
  apply Fintype.sum_equiv f.vertex
  intro v
  exact outdegree_iso f v

theorem universal_total {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) (A : Board (2*k+1)) :
    total A = total (Transform σ τ A) := by
  obtain ⟨f⟩ := h A
  exact total_iso f

theorem universal_start {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) (A : Board (2*k+1)) :
    L (start k) (A (start k)) = L (start k) (τ (A (σ (start k)))) := by
  obtain ⟨f⟩ := h A
  simpa only [f.beginning, Transform] using outdegree_iso f (start k)
end BoardV1
```

### Profiles.lean
```lean
import Board
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
namespace BoardV1
open scoped BigOperators

def single {n : ℕ} (v : Pos n) (d e : Dir) : Board n :=
  fun x => if x = v then d else e

theorem total_single_sub {n : ℕ} (v : Pos n) (d e : Dir) :
    total (single v d e) - total (n := n) (fun _ => e) = L v d - L v e := by
  classical
  unfold total
  rw [← Finset.sum_sub_distrib]
  have hh := Finset.sum_eq_single (s := Finset.univ)
    (f := fun x => L x (single v d e x) - L x e) v
    (fun x _ hx => by simp [single, hx]) (by simp)
  simpa [single] using hh

theorem transform_single {n : ℕ} (σ : Equiv.Perm (Pos n))
    (τ : Equiv.Perm Dir) (v : Pos n) (d e : Dir) :
    Transform σ τ (single (σ v) d e) = single v (τ d) (τ e) := by
  classical
  funext x
  simp only [Transform, single, σ.injective.eq_iff]
  split_ifs <;> rfl

theorem universal_variation {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) (v : Pos (2*k+1)) (d e : Dir) :
    L v (τ d) - L v (τ e) = L (σ v) d - L (σ v) e := by
  have h₁ := universal_total h (single (σ v) d e)
  have h₂ := universal_total h (fun _ => e)
  rw [transform_single] at h₁
  change total (fun _ => e) = total (fun _ => τ e) at h₂
  have h₃ := total_single_sub v (τ d) (τ e)
  have h₄ := total_single_sub (σ v) d e
  omega

theorem universal_offsets {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) :
    ∃ c : Pos (2*k+1) → ℤ, ∀ v d, L v (τ d) = L (σ v) d + c v := by
  refine ⟨fun v => L v (τ 0) - L (σ v) 0, ?_⟩
  intro v d
  have hv := universal_variation h v d 0
  dsimp
  omega

theorem universal_constant {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) (d : Dir) :
    (∑ v : Pos (2*k+1), L v d) = ∑ v : Pos (2*k+1), L v (τ d) :=
  universal_total h (fun _ => d)

theorem L_nonneg {n : ℕ} (v : Pos n) (d : Dir) : 0 ≤ L v d := by
  classical
  unfold L
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> omega

theorem L_ge_one {n : ℕ} {v w : Pos n} {d : Dir} (h : Ray v w d) :
    1 ≤ L v d := by
  classical
  unfold L
  have hh := Finset.single_le_sum
    (s := (Finset.univ : Finset (Pos n)))
    (f := fun w => if Ray v w d then (1 : ℤ) else 0)
    (fun _ _ => by split_ifs <;> omega) (Finset.mem_univ w)
  simpa only [ite_eq_left h] using hh

theorem north_start_zero (k : ℕ) : L (start k) 0 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (start k) w 0 := by
    rintro ⟨t, ht, hr, _⟩
    simp [row, start] at hr
    omega
  simp only [ite_eq_right hh]

theorem east_start_positive {k : ℕ} (hk : 1 ≤ k) : 1 ≤ L (start k) 2 := by
  apply L_ge_one (w := (⟨0, by omega⟩, ⟨1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [start, row, col]

theorem universal_fixes_start {k : ℕ} (hk : 1 ≤ k)
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) : σ (start k) = start k := by
  classical
  by_contra hs
  have hn := universal_start h (single (start k) 0 0)
  have he := universal_start h (single (start k) 2 0)
  simp [single, hs] at hn he
  have hz := north_start_zero k
  have hp := east_start_positive hk
  omega
end BoardV1
```

### Reflection.lean
```lean
import Profiles
import Mathlib.Tactic.FinCases
namespace BoardV1

def transposeD (d : Dir) : Dir :=
  match d.val with
  | 0 => 6 | 1 => 5 | 2 => 4 | 3 => 3
  | 4 => 2 | 5 => 1 | 6 => 0 | _ => 7

theorem transposeD_involutive : Function.Involutive transposeD := by
  intro d
  fin_cases d <;> rfl

def transposeDir : Equiv.Perm Dir :=
  ⟨transposeD, transposeD, transposeD_involutive, transposeD_involutive⟩

def transposePos (n : ℕ) : Equiv.Perm (Pos n) := Equiv.prodComm _ _

theorem row_transpose (d : Dir) : row (transposeDir d) = col d := by
  fin_cases d <;> rfl

theorem col_transpose (d : Dir) : col (transposeDir d) = row d := by
  fin_cases d <;> rfl

theorem transpose_ray {n : ℕ} (v w : Pos n) (d : Dir) :
    Ray v w d ↔ Ray (transposePos n v) (transposePos n w) (transposeDir d) := by
  simp only [Ray, transposePos, Equiv.prodComm_apply, row_transpose, col_transpose]
  constructor <;> rintro ⟨t, ht, hr, hc⟩ <;> exact ⟨t, ht, hc, hr⟩

def Reflection {n : ℕ} (A : Board n) : Board n :=
  Transform (transposePos n) transposeDir A

def reflectionIso {k : ℕ} (A : Board (2*k+1)) : RootedIso A (Reflection A) where
  vertex := transposePos _
  beginning := rfl
  ending := rfl
  edge_iff := by
    intro v w
    change Ray v w (A v) ↔
      Ray (transposePos _ v) (transposePos _ w) (transposeDir (A v))
    exact transpose_ray v w (A v)

theorem reflection_universal (k : ℕ) :
    Universal (transposePos (2*k+1)) transposeDir := fun A => ⟨reflectionIso A⟩

def identityIso {k : ℕ} (A : Board (2*k+1)) : RootedIso A A where
  vertex := Equiv.refl _
  beginning := rfl
  ending := rfl
  edge_iff := fun _ _ => Iff.rfl

theorem identity_universal (k : ℕ) :
    Universal (Equiv.refl (Pos (2*k+1))) (Equiv.refl Dir) := fun A => ⟨identityIso A⟩

theorem reflection_involutive {n : ℕ} : Function.Involutive (@Reflection n) := by
  intro A
  funext v
  exact transposeD_involutive (A v)

theorem ray_irreflexive {n : ℕ} (v : Pos n) (d : Dir) : ¬ Ray v v d := by
  rintro ⟨t, ht, hr, hc⟩
  fin_cases d <;> simp [row, col] at hr hc <;> omega
end BoardV1
```

### Cardinals.lean
```lean
import Reflection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
namespace BoardV1
open scoped BigOperators
noncomputable section
local instance rayDec {n : ℕ} (v : Pos n) (d : Dir) : DecidablePred (fun w => Ray v w d) := Classical.decPred _
local instance edgeDec {n : ℕ} (A : Board n) : DecidablePred (fun p : Pos n × Pos n => Edge A p.1 p.2) := Classical.decPred _

theorem L_card {n : ℕ} (v : Pos n) (d : Dir) :
    L v d = ((Finset.univ.filter (fun w => Ray v w d)).card : ℤ) := by
  classical
  simp [L, ← Finset.sum_boole]

theorem total_arc_card {n : ℕ} (A : Board n) :
    total A = ((Finset.univ.filter (fun p : Pos n × Pos n => Edge A p.1 p.2)).card : ℤ) := by
  classical
  unfold total L
  rw [← Fintype.sum_prod_type' ]
  simp only [Edge, Finset.sum_boole]
  congr 1

theorem ray_north {n : ℕ} (v w : Pos n) :
    Ray v w 0 ↔ w.1 < v.1 ∧ w.2 = v.2 := by
  constructor
  · rintro ⟨t, ht, hr, hc⟩
    simp [row, col] at hr hc
    constructor
    · change w.1.val < v.1.val
      omega
    · exact Fin.ext (by omega)
  · rintro ⟨hr, hc⟩
    refine ⟨v.1.val - w.1.val, by exact Nat.sub_pos_of_lt hr, ?_, ?_⟩
    · simp [row]
      have hh : w.1.val < v.1.val := hr
      omega
    · simp [col, hc]

theorem L_north {n : ℕ} (v : Pos n) : L v 0 = v.1.val := by
  classical
  unfold L
  simp_rw [ray_north]
  rw [Fintype.sum_prod_type]
  have hs : (∑ x : Fin n, ∑ y : Fin n, if x < v.1 ∧ y = v.2 then (1 : ℤ) else 0) =
      ∑ x : Fin n, if x < v.1 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x < v.1 <;> simp [h]
  rw [hs]
  have hh : (Finset.univ.filter (fun x : Fin n => x < v.1)) = Finset.Iio v.1 := by
    ext x
    simp
  rw [Finset.sum_boole, hh, Fin.card_Iio]
end
end BoardV1
```

### Rigidity.lean
```lean
import Cardinals
namespace BoardV1
open scoped BigOperators

theorem L_transpose {n : ℕ} (v : Pos n) (d : Dir) :
    L v d = L (transposePos n v) (transposeDir d) := by
  classical
  unfold L
  apply Fintype.sum_equiv (transposePos n)
  intro w
  rw [transpose_ray]

theorem L_west {n : ℕ} (v : Pos n) : L v 6 = v.2.val := by
  have h := L_transpose v 6
  change L v 6 = L (transposePos n v) 0 at h
  rw [L_north] at h
  exact h

theorem ray_south {n : ℕ} (v w : Pos n) :
    Ray v w 4 ↔ v.1 < w.1 ∧ w.2 = v.2 := by
  constructor
  · rintro ⟨t, ht, hr, hc⟩
    simp [row, col] at hr hc
    constructor
    · change v.1.val < w.1.val
      omega
    · exact Fin.ext (by omega)
  · rintro ⟨hr, hc⟩
    refine ⟨w.1.val - v.1.val, Nat.sub_pos_of_lt hr, ?_, ?_⟩
    · simp [row]
      have hh : v.1.val < w.1.val := hr
      omega
    · simp [col, hc]

theorem L_south {n : ℕ} (v : Pos n) : L v 4 = (n-1-v.1.val : ℕ) := by
  classical
  unfold L
  simp_rw [ray_south]
  rw [Fintype.sum_prod_type]
  have hs : (∑ x : Fin n, ∑ y : Fin n, if v.1 < x ∧ y = v.2 then (1 : ℤ) else 0) =
      ∑ x : Fin n, if v.1 < x then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : v.1 < x <;> simp [h]
  rw [hs]
  have hh : (Finset.univ.filter (fun x : Fin n => v.1 < x)) = Finset.Ioi v.1 := by
    ext x
    simp
  rw [Finset.sum_boole, hh, Fin.card_Ioi]

theorem L_east {n : ℕ} (v : Pos n) : L v 2 = (n-1-v.2.val : ℕ) := by
  have h := L_transpose v 2
  change L v 2 = L (transposePos n v) 4 at h
  rw [L_south] at h
  exact h

theorem opposite_cardinal_sums {n : ℕ} (v : Pos n) :
    L v 0 + L v 4 = (n-1 : ℕ) ∧ L v 2 + L v 6 = (n-1 : ℕ) := by
  rw [L_north, L_south, L_east, L_west]
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  constructor <;> omega

theorem normalized_positions {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ)
    (hN : τ 0 = 0) (hS : τ 4 = 4) (hW : τ 6 = 6) :
    σ = Equiv.refl _ := by
  obtain ⟨c, hc⟩ := universal_offsets h
  apply Equiv.ext
  intro v
  have h₁ := hc v 0
  have h₂ := hc v 4
  have h₃ := hc v 6
  rw [hN] at h₁
  rw [hS] at h₂
  rw [hW] at h₃
  have p := (opposite_cardinal_sums v).1
  have q := (opposite_cardinal_sums (σ v)).1
  have hz : c v = 0 := by omega
  rw [L_north, L_north, hz] at h₁
  rw [L_west, L_west, hz] at h₃
  apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

theorem universal_opposite_balance {k : ℕ} {σ : Equiv.Perm (Pos (2*k+1))}
    {τ : Equiv.Perm Dir} (h : Universal σ τ) (v : Pos (2*k+1)) :
    L v (τ 0) + L v (τ 4) = L v (τ 2) + L v (τ 6) := by
  obtain ⟨c, hc⟩ := universal_offsets h
  have p := opposite_cardinal_sums (σ v)
  have h₀ := hc v 0
  have h₄ := hc v 4
  have h₂ := hc v 2
  have h₆ := hc v 6
  omega
end BoardV1
```

### Corners.lean
```lean
import Rigidity
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace BoardV1
def corner00 (k : ℕ) : Pos (2*k+1) := (⟨0, by omega⟩, ⟨0, by omega⟩)
theorem corner00_0 (k : ℕ) : L (corner00 k) 0 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner00 k) w 0 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner00, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner00_1 (k : ℕ) : L (corner00 k) 1 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner00 k) w 1 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner00, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner00_2 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner00 k) 2 := by
  apply L_ge_one (w := (⟨0, by omega⟩, ⟨1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner00, row, col] <;> omega
theorem corner00_3 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner00 k) 3 := by
  apply L_ge_one (w := (⟨1, by omega⟩, ⟨1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner00, row, col] <;> omega
theorem corner00_4 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner00 k) 4 := by
  apply L_ge_one (w := (⟨1, by omega⟩, ⟨0, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner00, row, col] <;> omega
theorem corner00_5 (k : ℕ) : L (corner00 k) 5 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner00 k) w 5 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner00, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner00_6 (k : ℕ) : L (corner00 k) 6 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner00 k) w 6 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner00, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner00_7 (k : ℕ) : L (corner00 k) 7 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner00 k) w 7 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner00, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
def corner01 (k : ℕ) : Pos (2*k+1) := (⟨0, by omega⟩, ⟨2*k, by omega⟩)
theorem corner01_0 (k : ℕ) : L (corner01 k) 0 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner01 k) w 0 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner01, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner01_1 (k : ℕ) : L (corner01 k) 1 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner01 k) w 1 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner01, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner01_2 (k : ℕ) : L (corner01 k) 2 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner01 k) w 2 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner01, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner01_3 (k : ℕ) : L (corner01 k) 3 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner01 k) w 3 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner01, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner01_4 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner01 k) 4 := by
  apply L_ge_one (w := (⟨1, by omega⟩, ⟨2*k, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner01, row, col] <;> omega
theorem corner01_5 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner01 k) 5 := by
  apply L_ge_one (w := (⟨1, by omega⟩, ⟨2*k-1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner01, row, col] <;> omega
theorem corner01_6 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner01 k) 6 := by
  apply L_ge_one (w := (⟨0, by omega⟩, ⟨2*k-1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner01, row, col] <;> omega
theorem corner01_7 (k : ℕ) : L (corner01 k) 7 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner01 k) w 7 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner01, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
def corner10 (k : ℕ) : Pos (2*k+1) := (⟨2*k, by omega⟩, ⟨0, by omega⟩)
theorem corner10_0 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner10 k) 0 := by
  apply L_ge_one (w := (⟨2*k-1, by omega⟩, ⟨0, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner10, row, col] <;> omega
theorem corner10_1 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner10 k) 1 := by
  apply L_ge_one (w := (⟨2*k-1, by omega⟩, ⟨1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner10, row, col] <;> omega
theorem corner10_2 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner10 k) 2 := by
  apply L_ge_one (w := (⟨2*k, by omega⟩, ⟨1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner10, row, col] <;> omega
theorem corner10_3 (k : ℕ) : L (corner10 k) 3 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner10 k) w 3 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner10, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner10_4 (k : ℕ) : L (corner10 k) 4 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner10 k) w 4 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner10, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner10_5 (k : ℕ) : L (corner10 k) 5 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner10 k) w 5 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner10, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner10_6 (k : ℕ) : L (corner10 k) 6 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner10 k) w 6 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner10, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner10_7 (k : ℕ) : L (corner10 k) 7 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner10 k) w 7 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner10, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
def corner11 (k : ℕ) : Pos (2*k+1) := (⟨2*k, by omega⟩, ⟨2*k, by omega⟩)
theorem corner11_0 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner11 k) 0 := by
  apply L_ge_one (w := (⟨2*k-1, by omega⟩, ⟨2*k, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner11, row, col] <;> omega
theorem corner11_1 (k : ℕ) : L (corner11 k) 1 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner11 k) w 1 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner11, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner11_2 (k : ℕ) : L (corner11 k) 2 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner11 k) w 2 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner11, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner11_3 (k : ℕ) : L (corner11 k) 3 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner11 k) w 3 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner11, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner11_4 (k : ℕ) : L (corner11 k) 4 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner11 k) w 4 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner11, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner11_5 (k : ℕ) : L (corner11 k) 5 = 0 := by
  classical
  unfold L
  apply Finset.sum_eq_zero
  intro w _
  have hh : ¬ Ray (corner11 k) w 5 := by
    rintro ⟨t, ht, hr, hc⟩
    simp [corner11, row, col] at hr hc
    have h₁ := w.1.isLt
    have h₂ := w.2.isLt
    omega
  simp only [ite_eq_right hh]
theorem corner11_6 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner11 k) 6 := by
  apply L_ge_one (w := (⟨2*k, by omega⟩, ⟨2*k-1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner11, row, col] <;> omega
theorem corner11_7 (k : ℕ) (hk : 1 ≤ k) : 1 ≤ L (corner11 k) 7 := by
  apply L_ge_one (w := (⟨2*k-1, by omega⟩, ⟨2*k-1, by omega⟩))
  refine ⟨1, by omega, ?_, ?_⟩ <;> simp [corner11, row, col] <;> omega
theorem profile_injective {k : ℕ} (hk : 1 ≤ k) (d e : Dir)
    (h : ∀ v : Pos (2*k+1), L v d = L v e) : d = e := by
  fin_cases d <;> fin_cases e
  · rfl
  · have hh := h (corner11 k)
    change L (corner11 k) 0 = L (corner11 k) 1 at hh
    have hd := corner11_0 k hk
    have he := corner11_1 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 0 = L (corner00 k) 2 at hh
    have hd := corner00_0 k
    have he := corner00_2 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 0 = L (corner00 k) 3 at hh
    have hd := corner00_0 k
    have he := corner00_3 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 0 = L (corner00 k) 4 at hh
    have hd := corner00_0 k
    have he := corner00_4 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 0 = L (corner01 k) 5 at hh
    have hd := corner01_0 k
    have he := corner01_5 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 0 = L (corner01 k) 6 at hh
    have hd := corner01_0 k
    have he := corner01_6 k hk
    omega
  · have hh := h (corner10 k)
    change L (corner10 k) 0 = L (corner10 k) 7 at hh
    have hd := corner10_0 k hk
    have he := corner10_7 k
    omega
  · have hh := h (corner11 k)
    change L (corner11 k) 1 = L (corner11 k) 0 at hh
    have hd := corner11_1 k
    have he := corner11_0 k hk
    omega
  · rfl
  · have hh := h (corner00 k)
    change L (corner00 k) 1 = L (corner00 k) 2 at hh
    have hd := corner00_1 k
    have he := corner00_2 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 1 = L (corner00 k) 3 at hh
    have hd := corner00_1 k
    have he := corner00_3 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 1 = L (corner00 k) 4 at hh
    have hd := corner00_1 k
    have he := corner00_4 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 1 = L (corner01 k) 5 at hh
    have hd := corner01_1 k
    have he := corner01_5 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 1 = L (corner01 k) 6 at hh
    have hd := corner01_1 k
    have he := corner01_6 k hk
    omega
  · have hh := h (corner10 k)
    change L (corner10 k) 1 = L (corner10 k) 7 at hh
    have hd := corner10_1 k hk
    have he := corner10_7 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 2 = L (corner00 k) 0 at hh
    have hd := corner00_2 k hk
    have he := corner00_0 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 2 = L (corner00 k) 1 at hh
    have hd := corner00_2 k hk
    have he := corner00_1 k
    omega
  · rfl
  · have hh := h (corner10 k)
    change L (corner10 k) 2 = L (corner10 k) 3 at hh
    have hd := corner10_2 k hk
    have he := corner10_3 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 2 = L (corner01 k) 4 at hh
    have hd := corner01_2 k
    have he := corner01_4 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 2 = L (corner00 k) 5 at hh
    have hd := corner00_2 k hk
    have he := corner00_5 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 2 = L (corner00 k) 6 at hh
    have hd := corner00_2 k hk
    have he := corner00_6 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 2 = L (corner00 k) 7 at hh
    have hd := corner00_2 k hk
    have he := corner00_7 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 3 = L (corner00 k) 0 at hh
    have hd := corner00_3 k hk
    have he := corner00_0 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 3 = L (corner00 k) 1 at hh
    have hd := corner00_3 k hk
    have he := corner00_1 k
    omega
  · have hh := h (corner10 k)
    change L (corner10 k) 3 = L (corner10 k) 2 at hh
    have hd := corner10_3 k
    have he := corner10_2 k hk
    omega
  · rfl
  · have hh := h (corner01 k)
    change L (corner01 k) 3 = L (corner01 k) 4 at hh
    have hd := corner01_3 k
    have he := corner01_4 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 3 = L (corner00 k) 5 at hh
    have hd := corner00_3 k hk
    have he := corner00_5 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 3 = L (corner00 k) 6 at hh
    have hd := corner00_3 k hk
    have he := corner00_6 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 3 = L (corner00 k) 7 at hh
    have hd := corner00_3 k hk
    have he := corner00_7 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 4 = L (corner00 k) 0 at hh
    have hd := corner00_4 k hk
    have he := corner00_0 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 4 = L (corner00 k) 1 at hh
    have hd := corner00_4 k hk
    have he := corner00_1 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 4 = L (corner01 k) 2 at hh
    have hd := corner01_4 k hk
    have he := corner01_2 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 4 = L (corner01 k) 3 at hh
    have hd := corner01_4 k hk
    have he := corner01_3 k
    omega
  · rfl
  · have hh := h (corner00 k)
    change L (corner00 k) 4 = L (corner00 k) 5 at hh
    have hd := corner00_4 k hk
    have he := corner00_5 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 4 = L (corner00 k) 6 at hh
    have hd := corner00_4 k hk
    have he := corner00_6 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 4 = L (corner00 k) 7 at hh
    have hd := corner00_4 k hk
    have he := corner00_7 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 5 = L (corner01 k) 0 at hh
    have hd := corner01_5 k hk
    have he := corner01_0 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 5 = L (corner01 k) 1 at hh
    have hd := corner01_5 k hk
    have he := corner01_1 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 5 = L (corner00 k) 2 at hh
    have hd := corner00_5 k
    have he := corner00_2 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 5 = L (corner00 k) 3 at hh
    have hd := corner00_5 k
    have he := corner00_3 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 5 = L (corner00 k) 4 at hh
    have hd := corner00_5 k
    have he := corner00_4 k hk
    omega
  · rfl
  · have hh := h (corner11 k)
    change L (corner11 k) 5 = L (corner11 k) 6 at hh
    have hd := corner11_5 k
    have he := corner11_6 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 5 = L (corner01 k) 7 at hh
    have hd := corner01_5 k hk
    have he := corner01_7 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 6 = L (corner01 k) 0 at hh
    have hd := corner01_6 k hk
    have he := corner01_0 k
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 6 = L (corner01 k) 1 at hh
    have hd := corner01_6 k hk
    have he := corner01_1 k
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 6 = L (corner00 k) 2 at hh
    have hd := corner00_6 k
    have he := corner00_2 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 6 = L (corner00 k) 3 at hh
    have hd := corner00_6 k
    have he := corner00_3 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 6 = L (corner00 k) 4 at hh
    have hd := corner00_6 k
    have he := corner00_4 k hk
    omega
  · have hh := h (corner11 k)
    change L (corner11 k) 6 = L (corner11 k) 5 at hh
    have hd := corner11_6 k hk
    have he := corner11_5 k
    omega
  · rfl
  · have hh := h (corner01 k)
    change L (corner01 k) 6 = L (corner01 k) 7 at hh
    have hd := corner01_6 k hk
    have he := corner01_7 k
    omega
  · have hh := h (corner10 k)
    change L (corner10 k) 7 = L (corner10 k) 0 at hh
    have hd := corner10_7 k
    have he := corner10_0 k hk
    omega
  · have hh := h (corner10 k)
    change L (corner10 k) 7 = L (corner10 k) 1 at hh
    have hd := corner10_7 k
    have he := corner10_1 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 7 = L (corner00 k) 2 at hh
    have hd := corner00_7 k
    have he := corner00_2 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 7 = L (corner00 k) 3 at hh
    have hd := corner00_7 k
    have he := corner00_3 k hk
    omega
  · have hh := h (corner00 k)
    change L (corner00 k) 7 = L (corner00 k) 4 at hh
    have hd := corner00_7 k
    have he := corner00_4 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 7 = L (corner01 k) 5 at hh
    have hd := corner01_7 k
    have he := corner01_5 k hk
    omega
  · have hh := h (corner01 k)
    change L (corner01 k) 7 = L (corner01 k) 6 at hh
    have hd := corner01_7 k
    have he := corner01_6 k hk
    omega
  · rfl
end BoardV1
```

### Normalized.lean
```lean
import Corners
namespace BoardV1

theorem normalized_pair {k : ℕ} (hk : 1 ≤ k)
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) (hN : τ 0 = 0) (hS : τ 4 = 4) (hW : τ 6 = 6) :
    σ = Equiv.refl _ ∧ τ = Equiv.refl _ := by
  have hs := normalized_positions h hN hS hW
  refine ⟨hs, ?_⟩
  obtain ⟨c, hc⟩ := universal_offsets h
  apply Equiv.ext
  intro d
  apply profile_injective hk (τ d) d
  intro v
  have h₀ := hc v 0
  have hd := hc v d
  rw [hs, Equiv.refl_apply, hN] at h₀
  rw [hs, Equiv.refl_apply] at hd
  omega

def RootedIso.trans {k : ℕ} {A B C : Board (2*k+1)}
    (f : RootedIso A B) (g : RootedIso B C) : RootedIso A C where
  vertex := f.vertex.trans g.vertex
  beginning := by simp only [Equiv.trans_apply, f.beginning, g.beginning]
  ending := by simp only [Equiv.trans_apply, f.ending, g.ending]
  edge_iff := fun v w => (f.edge_iff v w).trans (g.edge_iff (f.vertex v) (f.vertex w))

theorem universal_reflection_normalize {k : ℕ}
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) :
    Universal ((transposePos _).trans σ) (τ.trans transposeDir) := by
  intro A
  obtain ⟨f⟩ := h A
  exact ⟨f.trans (reflectionIso (Transform σ τ A))⟩

/- Exact intended final proposition, deliberately only a definition.
   No theorem in this closure asserts it. The missing cardinal/geometric reduction
   cannot be supplied by treating normalized_pair as an unconditional classifier. -/
def LiteralEndpoint (k : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (Pos (2*k+1))) (τ : Equiv.Perm Dir),
    Universal σ τ ↔
      (Transform σ τ = (fun A => A)) ∨
      (Transform σ τ = @Reflection (2*k+1))
end BoardV1
```

### Separation.lean
```lean
import Normalized
namespace BoardV1
open scoped BigOperators
theorem ray_row_le {n : ℕ} (v : Pos n) (d c : Dir)
    (hr : row d = row c) (hn : row d ≠ 0) (hc : col c = 0) :
    L v d ≤ L v c := by
  classical
  rw [L_card, L_card]
  apply Int.ofNat_le.mpr
  exact Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun w => Ray v w d))
    (t := Finset.univ.filter (fun w => Ray v w c)) (fun w : Pos n => (w.1, v.2))
    (by
      intro w hw
      have hw' := (Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨t, ht, hrow, _⟩ := hw'
      exact ⟨t, ht, by simpa only [hr] using hrow, by simp [hc]⟩)
    (by
      intro w hw z hz he
      obtain ⟨t, _, hwr, hwc⟩ := (Finset.mem_filter.mp hw).2
      obtain ⟨u, _, hzr, hzc⟩ := (Finset.mem_filter.mp hz).2
      have heq : w.1 = z.1 := (Prod.mk.inj he).1
      have hmul : (t : ℤ) * row d = (u : ℤ) * row d := by
        rw [heq] at hwr
        omega
      have htu : (t : ℤ) = u := mul_right_cancel₀ hn hmul
      rw [htu] at hwc
      exact Prod.ext heq (Fin.ext (by omega)))
end BoardV1
```

### TotalSeparation.lean
```lean
import Separation
import Mathlib.Algebra.Order.Ring.Int
namespace BoardV1
open scoped BigOperators
noncomputable def revRows (n : ℕ) : Equiv.Perm (Pos n) where
  toFun v := (v.1.rev, v.2)
  invFun v := (v.1.rev, v.2)
  left_inv v := by simp
  right_inv v := by simp

theorem total_NS (n : ℕ) :
    (∑ v : Pos n, L v 0) = ∑ v : Pos n, L v 4 := by
  apply Fintype.sum_equiv (revRows n)
  intro v
  simp [L_north, L_south, revRows, Fin.rev]
  have hv := v.1.isLt
  omega

theorem total_transpose (n : ℕ) (d : Dir) :
    (∑ v : Pos n, L v d) = ∑ v : Pos n, L v (transposeDir d) := by
  apply Fintype.sum_equiv (transposePos n)
  intro v
  exact L_transpose v d

def IsCard (d : Dir) : Prop := d = 0 ∨ d = 2 ∨ d = 4 ∨ d = 6

theorem total_cardinal (n : ℕ) {d : Dir} (hd : IsCard d) :
    (∑ v : Pos n, L v d) = ∑ v : Pos n, L v 0 := by
  rcases hd with rfl | rfl | rfl | rfl
  · rfl
  · have h := total_transpose n 2
    change (∑ v : Pos n, L v 2) = ∑ v : Pos n, L v 4 at h
    exact h.trans (total_NS n).symm
  · exact (total_NS n).symm
  · exact total_transpose n 6

theorem diagonal_lt {k : ℕ} (hk : 1 ≤ k) {d : Dir} (hd : ¬ IsCard d) :
    (∑ v : Pos (2*k+1), L v d) < ∑ v : Pos (2*k+1), L v 0 := by
  classical
  fin_cases d
  all_goals try { exfalso; apply hd; unfold IsCard; decide }
  · apply Finset.sum_lt_sum
    · intro v _
      exact ray_row_le v 1 0 rfl (by decide) rfl
    · refine ⟨corner11 k, Finset.mem_univ _, ?_⟩
      have h := corner11_0 k hk
      change L (corner11 k) (1 : Dir) < L (corner11 k) 0
      rw [corner11_1]
      omega
  · rw [total_NS]
    apply Finset.sum_lt_sum
    · intro v _
      exact ray_row_le v 3 4 rfl (by decide) rfl
    · refine ⟨corner01 k, Finset.mem_univ _, ?_⟩
      have h := corner01_4 k hk
      change L (corner01 k) (3 : Dir) < L (corner01 k) 4
      rw [corner01_3]
      omega
  · rw [total_NS]
    apply Finset.sum_lt_sum
    · intro v _
      exact ray_row_le v 5 4 rfl (by decide) rfl
    · refine ⟨corner00 k, Finset.mem_univ _, ?_⟩
      have h := corner00_4 k hk
      change L (corner00 k) (5 : Dir) < L (corner00 k) 4
      rw [corner00_5]
      omega
  · apply Finset.sum_lt_sum
    · intro v _
      exact ray_row_le v 7 0 rfl (by decide) rfl
    · refine ⟨corner10 k, Finset.mem_univ _, ?_⟩
      have h := corner10_0 k hk
      change L (corner10 k) (7 : Dir) < L (corner10 k) 0
      rw [corner10_7]
      omega

theorem cardinal_preserved {k : ℕ} (hk : 1 ≤ k)
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) (d : Dir) : IsCard d ↔ IsCard (τ d) := by
  have ht := universal_constant h d
  constructor
  · intro hd
    by_contra hn
    have hl := diagonal_lt hk hn
    rw [← ht, total_cardinal _ hd] at hl
    exact (lt_irrefl _ hl)
  · intro hd
    by_contra hn
    have hl := diagonal_lt hk hn
    rw [ht, total_cardinal _ hd] at hl
    exact (lt_irrefl _ hl)
end BoardV1
```

### RootedCases.lean
```lean
import TotalSeparation
namespace BoardV1
theorem rooted_cardinal_cases {k : ℕ} (hk : 1 ≤ k)
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) :
    (τ 0=0 ∧ τ 4=4 ∧ τ 6=6) ∨
    (τ 0=6 ∧ τ 4=2 ∧ τ 6=0) := by
  have h0 := (cardinal_preserved hk h 0).mp (by simp [IsCard])
  have h2 := (cardinal_preserved hk h 2).mp (by simp [IsCard])
  have h4 := (cardinal_preserved hk h 4).mp (by simp [IsCard])
  have h6 := (cardinal_preserved hk h 6).mp (by simp [IsCard])
  have i02 : τ 0 ≠ τ 2 := τ.injective.ne (by decide)
  have i04 : τ 0 ≠ τ 4 := τ.injective.ne (by decide)
  have i06 : τ 0 ≠ τ 6 := τ.injective.ne (by decide)
  have i24 : τ 2 ≠ τ 4 := τ.injective.ne (by decide)
  have i26 : τ 2 ≠ τ 6 := τ.injective.ne (by decide)
  have i46 : τ 4 ≠ τ 6 := τ.injective.ne (by decide)
  have s0 := universal_start h (fun _ => (0 : Dir))
  have s2 := universal_start h (fun _ => (2 : Dir))
  have s4 := universal_start h (fun _ => (4 : Dir))
  have bal := universal_opposite_balance h (corner01 k)
  rcases h0 with h0 | h0 | h0 | h0 <;>
    rcases h2 with h2 | h2 | h2 | h2 <;>
    rcases h4 with h4 | h4 | h4 | h4 <;>
    rcases h6 with h6 | h6 | h6 | h6 <;>
    simp_all [L_north, L_south, L_east, L_west, start, corner01] <;> omega
end BoardV1
```

### Endpoint.lean
```lean
import RootedCases
namespace BoardV1
theorem universal_pair {k : ℕ} (hk : 1 ≤ k)
    {σ : Equiv.Perm (Pos (2*k+1))} {τ : Equiv.Perm Dir}
    (h : Universal σ τ) :
    (σ = Equiv.refl _ ∧ τ = Equiv.refl _) ∨
    (σ = transposePos _ ∧ τ = transposeDir) := by
  rcases rooted_cardinal_cases hk h with ⟨h0,h4,h6⟩ | ⟨h0,h4,h6⟩
  · exact Or.inl (normalized_pair hk h h0 h4 h6)
  · have hn := universal_reflection_normalize h
    have p := normalized_pair hk hn
      (by change transposeDir (τ 0) = 0; rw [h0]; rfl)
      (by change transposeDir (τ 4) = 4; rw [h4]; rfl)
      (by change transposeDir (τ 6) = 6; rw [h6]; rfl)
    right
    constructor
    · apply Equiv.ext
      intro v
      have q := congrArg (fun f : Equiv.Perm (Pos (2*k+1)) => f (transposePos _ v)) p.1
      simpa [Equiv.trans_apply, transposePos] using q
    · apply Equiv.ext
      intro d
      have q := congrArg (fun f : Equiv.Perm Dir => f d) p.2
      have r := congrArg transposeD q
      change transposeD (transposeD (τ d)) = transposeD d at r
      rw [transposeD_involutive (τ d)] at r
      exact r

theorem universal_iff_pair {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Pos (2*k+1))) (τ : Equiv.Perm Dir) :
    Universal σ τ ↔
    (σ = Equiv.refl _ ∧ τ = Equiv.refl _) ∨
    (σ = transposePos _ ∧ τ = transposeDir) := by
  constructor
  · exact universal_pair hk
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact identity_universal k
    · exact reflection_universal k

theorem literal_endpoint {k : ℕ} (hk : 1 ≤ k) : LiteralEndpoint k := by
  intro σ τ
  constructor
  · intro h
    rcases universal_pair hk h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left; rfl
    · right; rfl
  · rintro (h | h)
    · intro A
      have q := congrFun h A
      rw [q]
      exact ⟨identityIso A⟩
    · intro A
      have q := congrFun h A
      rw [q]
      exact ⟨reflectionIso A⟩

theorem all_odd_sizes (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ n = 2*k+1 ∧ LiteralEndpoint k := by
  obtain ⟨k,hk,rfl⟩ := (odd_size_bridge n).mp ⟨hn,h3⟩
  exact ⟨k,hk,rfl,literal_endpoint hk⟩

theorem source_map_set {k : ℕ} (hk : 1 ≤ k) :
    { S : Board (2*k+1) → Board (2*k+1) |
      ∃ σ τ, S = Transform σ τ ∧ Universal σ τ } =
    { (fun A => A), @Reflection (2*k+1) } := by
  ext S
  constructor
  · rintro ⟨σ,τ,rfl,h⟩
    exact (literal_endpoint hk σ τ).mp h
  · rintro (rfl | rfl)
    · exact ⟨Equiv.refl _, Equiv.refl _, rfl, identity_universal k⟩
    · exact ⟨transposePos _, transposeDir, rfl, reflection_universal k⟩
end BoardV1
```

### Action.lean
```lean
import Endpoint
namespace BoardV1
def boardAction {n : ℕ} (σ : Equiv.Perm (Pos n)) (τ : Equiv.Perm Dir) :
    Equiv.Perm (Board n) where
  toFun := Transform σ τ
  invFun := Transform σ.symm τ.symm
  left_inv A := by funext v; simp [Transform]
  right_inv A := by funext v; simp [Transform]

theorem action_faithful {k : ℕ}
    (σ ρ : Equiv.Perm (Pos (2*k+1))) (τ υ : Equiv.Perm Dir)
    (he : boardAction σ τ = boardAction ρ υ) : σ = ρ ∧ τ = υ := by
  have hd : ∀ (A : Board (2*k+1)) (v : Pos (2*k+1)), τ (A (σ v)) = υ (A (ρ v)) := by
    intro A v
    exact congrFun (congrArg (fun f : Equiv.Perm (Board (2*k+1)) => f A) he) v
  have ht : τ = υ := by
    apply Equiv.ext
    intro d
    exact hd (fun _ => d) (start k)
  subst υ
  refine ⟨?_,rfl⟩
  apply Equiv.ext
  intro v
  by_contra hn
  have hh := τ.injective (hd (single (σ v) 0 1) v)
  simp [single, Ne.symm hn] at hh

def SourceSym (k : ℕ) : Set (Equiv.Perm (Board (2*k+1))) :=
  { S | ∃ σ τ, S = boardAction σ τ ∧
      ∀ A, Nonempty (RootedIso A (S A)) }

theorem source_group_endpoint {k : ℕ} (hk : 1 ≤ k) :
    SourceSym k = { Equiv.refl _, boardAction (transposePos _) transposeDir } := by
  ext S
  constructor
  · rintro ⟨σ,τ,rfl,h⟩
    have hu : Universal σ τ := h
    rcases universal_pair hk hu with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨Equiv.refl _, Equiv.refl _, rfl, identity_universal k⟩
    · exact ⟨transposePos _, transposeDir, rfl, reflection_universal k⟩
end BoardV1
```

### AllSizes.lean
```lean
import Action
namespace BoardV1
theorem reflection_ne_identity (k : ℕ) :
    boardAction (transposePos (2*k+1)) transposeDir ≠
      Equiv.refl (Board (2*k+1)) := by
  intro h
  have q := congrArg (fun f : Equiv.Perm (Board (2*k+1)) =>
    f (fun _ => (0 : Dir)) (start k)) h
  change (6 : Dir) = 0 at q
  exact (by decide : (6 : Dir) ≠ 0) q

theorem all_odd_source_groups (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ n = 2*k+1 ∧
      SourceSym k = {Equiv.refl _, boardAction (transposePos _) transposeDir} := by
  obtain ⟨k,hk,rfl⟩ := (odd_size_bridge n).mp ⟨hn,h3⟩
  exact ⟨k,hk,rfl,source_group_endpoint hk⟩
end BoardV1
```

### Audit.lean
```lean
import Normalized
#print axioms BoardV1.Pos
#print axioms BoardV1.Dir
#print axioms BoardV1.Board
#print axioms BoardV1.row
#print axioms BoardV1.col
#print axioms BoardV1.Ray
#print axioms BoardV1.Edge
#print axioms BoardV1.Transform
#print axioms BoardV1.start
#print axioms BoardV1.center
#print axioms BoardV1.RootedIso
#print axioms BoardV1.Universal
#print axioms BoardV1.L
#print axioms BoardV1.total
#print axioms BoardV1.odd_size_bridge
#print axioms BoardV1.outdegree_iso
#print axioms BoardV1.total_iso
#print axioms BoardV1.universal_total
#print axioms BoardV1.universal_start
#print axioms BoardV1.single
#print axioms BoardV1.total_single_sub
#print axioms BoardV1.transform_single
#print axioms BoardV1.universal_variation
#print axioms BoardV1.universal_offsets
#print axioms BoardV1.universal_constant
#print axioms BoardV1.L_nonneg
#print axioms BoardV1.L_ge_one
#print axioms BoardV1.north_start_zero
#print axioms BoardV1.east_start_positive
#print axioms BoardV1.universal_fixes_start
#print axioms BoardV1.transposeD
#print axioms BoardV1.transposeD_involutive
#print axioms BoardV1.transposeDir
#print axioms BoardV1.transposePos
#print axioms BoardV1.row_transpose
#print axioms BoardV1.col_transpose
#print axioms BoardV1.transpose_ray
#print axioms BoardV1.Reflection
#print axioms BoardV1.reflectionIso
#print axioms BoardV1.reflection_universal
#print axioms BoardV1.identityIso
#print axioms BoardV1.identity_universal
#print axioms BoardV1.reflection_involutive
#print axioms BoardV1.ray_irreflexive
#print axioms BoardV1.L_card
#print axioms BoardV1.total_arc_card
#print axioms BoardV1.ray_north
#print axioms BoardV1.L_north
#print axioms BoardV1.L_transpose
#print axioms BoardV1.L_west
#print axioms BoardV1.ray_south
#print axioms BoardV1.L_south
#print axioms BoardV1.L_east
#print axioms BoardV1.opposite_cardinal_sums
#print axioms BoardV1.normalized_positions
#print axioms BoardV1.universal_opposite_balance
#print axioms BoardV1.corner00
#print axioms BoardV1.corner00_0
#print axioms BoardV1.corner00_1
#print axioms BoardV1.corner00_2
#print axioms BoardV1.corner00_3
#print axioms BoardV1.corner00_4
#print axioms BoardV1.corner00_5
#print axioms BoardV1.corner00_6
#print axioms BoardV1.corner00_7
#print axioms BoardV1.corner01
#print axioms BoardV1.corner01_0
#print axioms BoardV1.corner01_1
#print axioms BoardV1.corner01_2
#print axioms BoardV1.corner01_3
#print axioms BoardV1.corner01_4
#print axioms BoardV1.corner01_5
#print axioms BoardV1.corner01_6
#print axioms BoardV1.corner01_7
#print axioms BoardV1.corner10
#print axioms BoardV1.corner10_0
#print axioms BoardV1.corner10_1
#print axioms BoardV1.corner10_2
#print axioms BoardV1.corner10_3
#print axioms BoardV1.corner10_4
#print axioms BoardV1.corner10_5
#print axioms BoardV1.corner10_6
#print axioms BoardV1.corner10_7
#print axioms BoardV1.corner11
#print axioms BoardV1.corner11_0
#print axioms BoardV1.corner11_1
#print axioms BoardV1.corner11_2
#print axioms BoardV1.corner11_3
#print axioms BoardV1.corner11_4
#print axioms BoardV1.corner11_5
#print axioms BoardV1.corner11_6
#print axioms BoardV1.corner11_7
#print axioms BoardV1.profile_injective
#print axioms BoardV1.normalized_pair
#print axioms BoardV1.RootedIso.trans
#print axioms BoardV1.universal_reflection_normalize
#print axioms BoardV1.LiteralEndpoint
```

### FinalAudit.lean
```lean
import Action
#print axioms BoardV1.Pos
#print axioms BoardV1.Dir
#print axioms BoardV1.Board
#print axioms BoardV1.row
#print axioms BoardV1.col
#print axioms BoardV1.Ray
#print axioms BoardV1.Edge
#print axioms BoardV1.Transform
#print axioms BoardV1.start
#print axioms BoardV1.center
#print axioms BoardV1.RootedIso
#print axioms BoardV1.Universal
#print axioms BoardV1.L
#print axioms BoardV1.total
#print axioms BoardV1.odd_size_bridge
#print axioms BoardV1.outdegree_iso
#print axioms BoardV1.total_iso
#print axioms BoardV1.universal_total
#print axioms BoardV1.universal_start
#print axioms BoardV1.single
#print axioms BoardV1.total_single_sub
#print axioms BoardV1.transform_single
#print axioms BoardV1.universal_variation
#print axioms BoardV1.universal_offsets
#print axioms BoardV1.universal_constant
#print axioms BoardV1.L_nonneg
#print axioms BoardV1.L_ge_one
#print axioms BoardV1.north_start_zero
#print axioms BoardV1.east_start_positive
#print axioms BoardV1.universal_fixes_start
#print axioms BoardV1.transposeD
#print axioms BoardV1.transposeD_involutive
#print axioms BoardV1.transposeDir
#print axioms BoardV1.transposePos
#print axioms BoardV1.row_transpose
#print axioms BoardV1.col_transpose
#print axioms BoardV1.transpose_ray
#print axioms BoardV1.Reflection
#print axioms BoardV1.reflectionIso
#print axioms BoardV1.reflection_universal
#print axioms BoardV1.identityIso
#print axioms BoardV1.identity_universal
#print axioms BoardV1.reflection_involutive
#print axioms BoardV1.ray_irreflexive
#print axioms BoardV1.L_card
#print axioms BoardV1.total_arc_card
#print axioms BoardV1.ray_north
#print axioms BoardV1.L_north
#print axioms BoardV1.L_transpose
#print axioms BoardV1.L_west
#print axioms BoardV1.ray_south
#print axioms BoardV1.L_south
#print axioms BoardV1.L_east
#print axioms BoardV1.opposite_cardinal_sums
#print axioms BoardV1.normalized_positions
#print axioms BoardV1.universal_opposite_balance
#print axioms BoardV1.corner00
#print axioms BoardV1.corner00_0
#print axioms BoardV1.corner00_1
#print axioms BoardV1.corner00_2
#print axioms BoardV1.corner00_3
#print axioms BoardV1.corner00_4
#print axioms BoardV1.corner00_5
#print axioms BoardV1.corner00_6
#print axioms BoardV1.corner00_7
#print axioms BoardV1.corner01
#print axioms BoardV1.corner01_0
#print axioms BoardV1.corner01_1
#print axioms BoardV1.corner01_2
#print axioms BoardV1.corner01_3
#print axioms BoardV1.corner01_4
#print axioms BoardV1.corner01_5
#print axioms BoardV1.corner01_6
#print axioms BoardV1.corner01_7
#print axioms BoardV1.corner10
#print axioms BoardV1.corner10_0
#print axioms BoardV1.corner10_1
#print axioms BoardV1.corner10_2
#print axioms BoardV1.corner10_3
#print axioms BoardV1.corner10_4
#print axioms BoardV1.corner10_5
#print axioms BoardV1.corner10_6
#print axioms BoardV1.corner10_7
#print axioms BoardV1.corner11
#print axioms BoardV1.corner11_0
#print axioms BoardV1.corner11_1
#print axioms BoardV1.corner11_2
#print axioms BoardV1.corner11_3
#print axioms BoardV1.corner11_4
#print axioms BoardV1.corner11_5
#print axioms BoardV1.corner11_6
#print axioms BoardV1.corner11_7
#print axioms BoardV1.profile_injective
#print axioms BoardV1.normalized_pair
#print axioms BoardV1.RootedIso.trans
#print axioms BoardV1.universal_reflection_normalize
#print axioms BoardV1.LiteralEndpoint
#print axioms BoardV1.ray_row_le
#print axioms BoardV1.revRows
#print axioms BoardV1.total_NS
#print axioms BoardV1.total_transpose
#print axioms BoardV1.IsCard
#print axioms BoardV1.total_cardinal
#print axioms BoardV1.diagonal_lt
#print axioms BoardV1.cardinal_preserved
#print axioms BoardV1.rooted_cardinal_cases
#print axioms BoardV1.universal_pair
#print axioms BoardV1.universal_iff_pair
#print axioms BoardV1.literal_endpoint
#print axioms BoardV1.all_odd_sizes
#print axioms BoardV1.source_map_set
#print axioms BoardV1.boardAction
#print axioms BoardV1.action_faithful
#print axioms BoardV1.SourceSym
#print axioms BoardV1.source_group_endpoint
set_option pp.all true in
#print BoardV1.source_group_endpoint
set_option pp.all true in
#print BoardV1.literal_endpoint
```

### ExpandedAudit.lean
```lean
import AllSizes
#print axioms BoardV1.Pos
#print axioms BoardV1.Dir
#print axioms BoardV1.Board
#print axioms BoardV1.row
#print axioms BoardV1.col
#print axioms BoardV1.Ray
#print axioms BoardV1.Edge
#print axioms BoardV1.Transform
#print axioms BoardV1.start
#print axioms BoardV1.center
#print axioms BoardV1.RootedIso
#print axioms BoardV1.Universal
#print axioms BoardV1.L
#print axioms BoardV1.total
#print axioms BoardV1.odd_size_bridge
#print axioms BoardV1.outdegree_iso
#print axioms BoardV1.total_iso
#print axioms BoardV1.universal_total
#print axioms BoardV1.universal_start
#print axioms BoardV1.single
#print axioms BoardV1.total_single_sub
#print axioms BoardV1.transform_single
#print axioms BoardV1.universal_variation
#print axioms BoardV1.universal_offsets
#print axioms BoardV1.universal_constant
#print axioms BoardV1.L_nonneg
#print axioms BoardV1.L_ge_one
#print axioms BoardV1.north_start_zero
#print axioms BoardV1.east_start_positive
#print axioms BoardV1.universal_fixes_start
#print axioms BoardV1.transposeD
#print axioms BoardV1.transposeD_involutive
#print axioms BoardV1.transposeDir
#print axioms BoardV1.transposePos
#print axioms BoardV1.row_transpose
#print axioms BoardV1.col_transpose
#print axioms BoardV1.transpose_ray
#print axioms BoardV1.Reflection
#print axioms BoardV1.reflectionIso
#print axioms BoardV1.reflection_universal
#print axioms BoardV1.identityIso
#print axioms BoardV1.identity_universal
#print axioms BoardV1.reflection_involutive
#print axioms BoardV1.ray_irreflexive
#print axioms BoardV1.L_card
#print axioms BoardV1.total_arc_card
#print axioms BoardV1.ray_north
#print axioms BoardV1.L_north
#print axioms BoardV1.L_transpose
#print axioms BoardV1.L_west
#print axioms BoardV1.ray_south
#print axioms BoardV1.L_south
#print axioms BoardV1.L_east
#print axioms BoardV1.opposite_cardinal_sums
#print axioms BoardV1.normalized_positions
#print axioms BoardV1.universal_opposite_balance
#print axioms BoardV1.corner00
#print axioms BoardV1.corner00_0
#print axioms BoardV1.corner00_1
#print axioms BoardV1.corner00_2
#print axioms BoardV1.corner00_3
#print axioms BoardV1.corner00_4
#print axioms BoardV1.corner00_5
#print axioms BoardV1.corner00_6
#print axioms BoardV1.corner00_7
#print axioms BoardV1.corner01
#print axioms BoardV1.corner01_0
#print axioms BoardV1.corner01_1
#print axioms BoardV1.corner01_2
#print axioms BoardV1.corner01_3
#print axioms BoardV1.corner01_4
#print axioms BoardV1.corner01_5
#print axioms BoardV1.corner01_6
#print axioms BoardV1.corner01_7
#print axioms BoardV1.corner10
#print axioms BoardV1.corner10_0
#print axioms BoardV1.corner10_1
#print axioms BoardV1.corner10_2
#print axioms BoardV1.corner10_3
#print axioms BoardV1.corner10_4
#print axioms BoardV1.corner10_5
#print axioms BoardV1.corner10_6
#print axioms BoardV1.corner10_7
#print axioms BoardV1.corner11
#print axioms BoardV1.corner11_0
#print axioms BoardV1.corner11_1
#print axioms BoardV1.corner11_2
#print axioms BoardV1.corner11_3
#print axioms BoardV1.corner11_4
#print axioms BoardV1.corner11_5
#print axioms BoardV1.corner11_6
#print axioms BoardV1.corner11_7
#print axioms BoardV1.profile_injective
#print axioms BoardV1.normalized_pair
#print axioms BoardV1.RootedIso.trans
#print axioms BoardV1.universal_reflection_normalize
#print axioms BoardV1.LiteralEndpoint
#print axioms BoardV1.ray_row_le
#print axioms BoardV1.revRows
#print axioms BoardV1.total_NS
#print axioms BoardV1.total_transpose
#print axioms BoardV1.IsCard
#print axioms BoardV1.total_cardinal
#print axioms BoardV1.diagonal_lt
#print axioms BoardV1.cardinal_preserved
#print axioms BoardV1.rooted_cardinal_cases
#print axioms BoardV1.universal_pair
#print axioms BoardV1.universal_iff_pair
#print axioms BoardV1.literal_endpoint
#print axioms BoardV1.all_odd_sizes
#print axioms BoardV1.source_map_set
#print axioms BoardV1.boardAction
#print axioms BoardV1.action_faithful
#print axioms BoardV1.SourceSym
#print axioms BoardV1.source_group_endpoint
#print axioms BoardV1.reflection_ne_identity
#print axioms BoardV1.all_odd_source_groups
set_option pp.all true in
#print BoardV1.Universal
set_option pp.all true in
#print BoardV1.RootedIso
set_option pp.all true in
#print BoardV1.LiteralEndpoint
set_option pp.all true in
#print BoardV1.SourceSym
set_option pp.all true in
#print BoardV1.all_odd_source_groups
set_option pp.all true in
#print BoardV1.source_group_endpoint
set_option pp.all true in
#print BoardV1.universal_pair
```
