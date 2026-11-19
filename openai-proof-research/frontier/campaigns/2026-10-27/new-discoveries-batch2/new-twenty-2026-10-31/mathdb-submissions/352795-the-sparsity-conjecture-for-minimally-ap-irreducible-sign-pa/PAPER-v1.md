# A nine-entry counterexample to the minimally AP-irreducible sparsity conjecture

Version 1, 15 November 2026. Target: MathDB 352795; source: Sunil Das, *Sign patterns that allow algebraic positivity*, arXiv:2112.00442v3, Section 3 and Conjecture 5.1. This is a standalone refutation of that precise source statement. It makes no assertion about the present published status, worldwide priority, or the unread journal-final body.

## Definitions and assertion

Let n be a positive integer. A sign pattern is a function on {1,...,n} squared taking the three values 0,+,-. Its directed support has the arc i to j precisely when its entry at (i,j) is nonzero. Reducibility means that a simultaneous permutation of rows and columns gives two nonempty diagonal blocks with a zero off-diagonal rectangular block. We use the upper-right zero block convention; interchanging the blocks gives the other convention. Irreducibility is its negation. This definition does not impose numerical nonnegativity on a signed matrix.

For completeness, a support relation R is reducible exactly when there is a nonempty proper subset S with no arc from S to its complement. A permutation with a zero upper-right block supplies S as the first block. Conversely, enumerate S first and its complement second. This is a bijective ordering of all n indices and therefore a simultaneous permutation, and its upper-right block is zero. This proves both directions, including the nonempty and proper requirements. In Lean, `block_cut` proves this using finite subtype equivalences. `block_permutation` transports the two-block ordering to contiguous Fin k and Fin l indices in Fin(k+l); `block_order` proves k+l=n. Thus no change of matrix order or undirected substitute is involved.

Use the canonical numerical representative 0,1,-1 of each sign. It has exactly the stated sign and exactly the same support. Aplus keeps positive entries and sets all others to zero. Aminus keeps NEGATIVE entries and sets all others to zero. Define the literal integer matrix B by B(i,j)=Aplus(i,j)-Aminus(j,i). Consequently B(i,j) is the sum of the two indicators A(i,j)=+ and A(j,i)=-. Its support is exactly their logical OR. If both conditions hold, the weight is 2, not 0. More generally, any numerical representatives of the given signs give two nonnegative contributions, strictly positive exactly in these same cases. Hence this canonical integer construction faithfully computes the source's sign/support B for every sign pattern. No magnitude choice affects irreducibility.

The source AP condition means: A is irreducible, every row has a positive, every column has a positive, and B is irreducible. Minimality means AP holds and replacing ANY ONE nonzero entry with zero destroys AP. We use precisely this single-erasure definition, without substituting a stronger proper-subpattern predicate. The zero-diagonal condition means every diagonal entry equals zero. The number of entries is the cardinality of the actual nonzero support.

Conjecture 5.1 asserts the universal bound nnz(A)<=2n-2 for every positive order and every minimally AP-irreducible zero-diagonal sign pattern. Actual numerical algebraic positivity is not an extra hypothesis: that is the distinct subject of Conjecture 5.2.

## Construction and exact support

All displayed indices in this paper are one-based; Lean Fin indices are one less.

```
A = [ 0  0  0  0  +
      0  0  -  +  0
      0  +  0  0  -
      0  +  0  0  0
      +  -  +  0  0 ]

canonical B = [ 0  0  0  0  1
                0  0  0  1  1
                0  2  0  0  0
                0  1  0  0  0
                1  0  2  0  0 ]
```

The complete outgoing support lists are:

| Vertex | A | B |
|---|---|---|
| 1 | 5 | 5 |
| 2 | 3,4 | 4,5 |
| 3 | 2,5 | 2 |
| 4 | 2 | 2 |
| 5 | 1,2,3 | 1,3 |

A has the six positives (1,5),(2,4),(3,2),(4,2),(5,1),(5,3) and the three negatives (2,3),(3,5),(5,2). These are distinct, none is diagonal, and all other entries are zero. Thus nnz(A)=9. The weights B(3,2)=B(5,3)=2 explicitly account for the overlaps.

## AP-irreducibility

Each row has a positive. Columns 1,2,3,4,5 have positives in rows 5,3,5,2,1 respectively. Both directed support relations have directed walks to and from vertex 2, as listed below; the empty walk is used at vertex 2 itself.

| Vertex v | A: v to 2 | A: 2 to v | B: v to 2 | B: 2 to v |
|---|---|---|---|---|
| 1 | 1,5,2 | 2,3,5,1 | 1,5,3,2 | 2,5,1 |
| 2 | 2 | 2 | 2 | 2 |
| 3 | 3,2 | 2,3 | 3,2 | 2,5,3 |
| 4 | 4,2 | 2,4 | 4,2 | 2,4 |
| 5 | 5,2 | 2,3,5 | 5,3,2 | 2,5 |

Every consecutive pair appears in the complete support table. Concatenation gives a directed walk between every two vertices. A nonempty proper closed cut cannot then exist: start inside it and end outside it, and consider the first exiting arc of such a walk. This contradicts closure. The block/cut equivalence proves irreducibility of A and B. This argument needs no positive-length walk from a vertex to itself and invokes no numerical nonnegative-matrix irreducibility theorem. Therefore A is AP-irreducible. The formal proof instead checks the equivalent finite cut conditions directly, over only 32 Boolean subsets of five indices.

## Every deletion fails

The following table accounts for every nonzero position, with no change of candidate.

| Erased position/sign | Obstruction |
|---|---|
| (1,5),+ | row 1 loses its sole positive |
| (2,4),+ | row 2 loses its sole positive |
| (3,2),+ | row 3 loses its sole positive |
| (4,2),+ | row 4 loses its sole positive |
| (5,1),+ | column 1 loses its sole positive |
| (5,3),+ | column 3 loses its sole positive |
| (2,3),- | S={2,4} is closed in the erased A |
| (3,5),- | S={2,3,4} is closed in the erased A |
| (5,2),- | S={2,4} is closed in B of the erased A |

For the first negative erasure, the complete remaining outgoing lists within S are 2 to {4} and 4 to {2}. For the second they are 2 to {3,4}, 3 to {2}, 4 to {2}. For the third erasure, recompute B from the erased SIGN pattern: the reverse contribution 2 to 5 disappears, leaving in S the lists 2 to {4}, 4 to {2}. Each S is nonempty and excludes vertex 1, so each supplies an actual proper zero block after permutation. For example, use orders (2,4,1,3,5) and (2,3,4,1,5) for the respective cuts. In particular the third case concerns B, not an unjustified deletion of an undirected edge. The other negative contributions overlapping existing positives keep their weight-1 support after deletion, as the literal B definition requires.

Thus each of the nine erasures fails at least one source AP condition. Together with AP itself, this proves source minimality. The matrix has zero diagonal, order 5, and 9>2*5-2=8 nonzeros. It is therefore a counterexample. Instantiating the unchanged universal assertion at order 5 proves its negation at arbitrary positive order; the same witness also refutes the version restricted to n>=2. No finite sampling is being used to prove a universal positive claim.

## Statement and dependency map

| Source requirement | Lean definition/proof |
|---|---|
| three-valued arbitrary-order patterns | Sign, Pattern |
| signed directed nonzero support | support, representative_sign |
| exact simultaneous block permutation | BlockReducible, block_permutation, block_order |
| closed cuts equivalent to source blocks | block_cut, irred_cut |
| literal Aplus minus transpose(Aminus) | Aplus, Aminus, B, B_support |
| row AND column coverage; both irreducibilities | AP, finiteAP_iff, actual_AP |
| actual single-entry erasure and all nine failures | erase, all_deletions, actual_minimal |
| actual support cardinality and zero diagonal | nnz, actual_nnz, actual_diagonal |
| overlapping B weights | overlap_weights |
| unconditional witness and full negation | witness, refutation |
| every custom predicate expanded in full universal negation | APRefutation.expanded_refutation |

No custom source bridge is assumed as a hypothesis. The expanded audit statement literally quantifies functions Fin n -> Fin n -> Sign, explicit two-block equivalences, the two numerical indicator contributions, the erased function, the support filter cardinality, and the diagonal equations. Its proof is definitionally the unconditional refutation. All theorem dependencies are kernel checked; no native_decide, unsafe code, new axioms, sorry or admit occurs in production sources. Only propext, Classical.choice and Quot.sound occur in the audited transitive axioms.

## Scope, SELF review, and process limits

The source mathematical dependency is limited to definitions and the conjecture in the supplied lawful v3 copy, not the source's theorems about algebraically positive matrices. Page 10 definitions, page 12 Lemma 3.10 and page 22 conjectures were rendered and visually inspected with installed Poppler. The raw target record was read in full. The supplied independent PASS and bounded SUBSTANTIAL judgment are inherited unchanged, not a new independent judgment by this implementation author. Released 109/14/373 comparisons remain bounded root-supplied coverage; their full bodies were not personally reread. The final published article and original registry/accepted proof bodies remain unread and unaccessed. No global absence or present publication-status claim follows.

Hostile checks: the support is directed; positive coverage is both row and column; the negative part retains the negative sign; both overlaps give 2; deletion recomputes B from the sign pattern; all nine entries and all zero positions are accounted for; finite cuts are semantically transported to exact blocks; the endpoint has no source-bridge assumptions. The use of Boolean subsets is only a finite method for this fixed witness, not a redefinition of irreducibility. Source minimality is the explicit single-erasure notion, so no unproved monotonic-equivalence assertion is needed. There is no remaining mathematical bridge gap in these modules. Independent extraction/review remains an external acceptance gate.

All inherited producer, reviewer and root defects remain UNWAIVED. In particular the supplied reviewer records earlier payload overruns, clipped narrative display, late override reading, unnecessary control displays, and an arXiv crawl interval violation. This implementation also retains defects: an initial unnecessary pwd command, a failed TASK filename read before locating TASK.txt, initial direct interface reading, multiple documentary payload/logical-unit overruns (including read01, read12, std03, result07), and the initially unbounded formal f01 display. The first executable SETUP was bootstrap, followed by standalone frozen-before; these facts do not erase the preceding read/control commands. The broad screen included unrelated arXiv alias matches and displayed part of that aggregate; a narrower exact-identity projection followed. These are not excused by the unlimited cumulative-reading clarification. No process-clean PASS is asserted.

Current usage is documented in the handoff and full receipts. Acquisition, search and scientific prototypes are all zero in this lane. Only formal wrapper invocations consume the separate fresh 64-call allocation; failures count. No children, installs, author code, project caches from other lanes, git, shared ledgers, accounts, messages, publication or uploads were used. Counts remain 70/80 NEW and 109 total; no acceptance or credit is reported.

## Reproducible formal appendix

Dependency order: Source, Witness, Audit. Each following LEAN-FILE block is the complete literal UTF-8 source, including its final newline. No other project source, olean or cache is a dependency. The source hashes below are authoritative for extraction. Save each block as src/NAME.lean and verify SHA256 before compilation. An extractor is provided after the blocks.

The verified pinned binary hashes and package paths are reproduced below. The Lean version is pinned as 4.34.1; source release revision is d13f23b723b8a846827a245b89c10fc7d3f11612. The frozen wrapper validates both executable hashes on every call. Upstream standard compiled libraries are trusted pinned dependencies; their full olean origins were not independently attested. The eight-package dependency metadata is in the reproduced pin object. No unowned project artifact is used.

```json
{
  "lean_version": "4.34.1",
  "mathlib_revision": "d13f23b723b8a846827a245b89c10fc7d3f11612",
  "lean_bin": "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
  "lean_sha256": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
  "leanchecker_bin": "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
  "leanchecker_sha256": "ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe",
  "packages_root": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages",
  "upstream_lean_paths": [
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean",
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean"
  ],
  "mathlib_source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib",
  "mathlib_metadata_sha256": {
    "Mathlib.lean": "61d699d8ace6240934a751f1b1951339090d6e380b505041632227dd7eb73a29",
    "lake-manifest.json": "8f67b2cf24143ac091cdb425e886c2164b2fc2d6fbccd6db9454b697f9541a67"
  },
  "pin_limits": "Root hashed binaries and available upstream source metadata, did NOT execute Lean/git or attest all upstream olean origins. Worker verifies runtime version/pin metadata before compilation; accepted pinned upstream oleans trusted. Never overwrite PINS.json; record discovered verification limits separately."
}
```

<!-- LEAN-FILE Source.lean SHA256 2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6 -->
```lean
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Card

namespace APRefutation
inductive Sign where
  | zero | pos | neg
  deriving DecidableEq
abbrev Pattern (n : ℕ) := Fin n → Fin n → Sign
def support {n} (A : Pattern n) (i j : Fin n) : Prop := A i j ≠ .zero
-- An ordered two-block decomposition: equivalently a simultaneous permutation.
def BlockReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n,
    ∀ i j, ¬ R (e (.inl i)) (e (.inr j))
def CutReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ s : Fin n → Bool, (∃ i, s i = true) ∧ (∃ j, s j = false) ∧
    ∀ i j, s i = true → s j = false → ¬ R i j

theorem block_cut {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ CutReducible R := by
  classical
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    let s : Fin n → Bool := fun x => (e.symm x).isLeft
    refine ⟨s, ⟨e (.inl ⟨0,hk⟩), ?_⟩, ⟨e (.inr ⟨0,hl⟩), ?_⟩, ?_⟩
    · simp [s]
    · simp [s]
    · intro i j hi hj
      obtain ⟨x, rfl⟩ := e.surjective i
      obtain ⟨y, rfl⟩ := e.surjective j
      cases x with
      | inl a =>
        cases y with
        | inl b => simp [s] at hj
        | inr b => exact h a b
      | inr a => simp [s] at hi
  · rintro ⟨s,⟨a,ha⟩,⟨b,hb⟩,h⟩
    let S : Set (Fin n) := {x | s x = true}
    let T : Set (Fin n) := Sᶜ
    have hb' : b ∈ T := by simp [T,S,hb]
    let : Nonempty S := ⟨⟨a,ha⟩⟩
    let : Nonempty T := ⟨⟨b,hb'⟩⟩
    let e := (Equiv.sumCongr (Fintype.equivFin S).symm
      (Fintype.equivFin T).symm).trans (Equiv.Set.sumCompl S)
    refine ⟨Fintype.card S, Fintype.card T, Fintype.card_pos,
      Fintype.card_pos, e, ?_⟩
    intro i j
    apply h
    · exact ((Fintype.equivFin S).symm i).property
    · have := ((Fintype.equivFin T).symm j).property
      change s (↑((Fintype.equivFin T).symm j)) = false
      change s (↑((Fintype.equivFin T).symm j)) ≠ true at this
      cases hv : s (↑((Fintype.equivFin T).symm j)) <;> simp_all

-- Literal contiguous zero block after a simultaneous permutation of the indices.
theorem block_permutation {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      ∃ e : Fin (k+l) ≃ Fin n,
        ∀ i : Fin k, ∀ j : Fin l, ¬ R (e (Fin.castAdd l i)) (e (Fin.natAdd k j)) := by
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.symm.trans e,by simpa using h⟩
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.trans e,by simpa using h⟩

theorem block_order {n k l} (e : Fin (k+l) ≃ Fin n) : k+l=n := by
  simpa using Fintype.card_congr e

def Irreducible {n} (R : Fin n → Fin n → Prop) := ¬ BlockReducible R

def representative : Sign → ℤ
  | .zero => 0 | .pos => 1 | .neg => -1
def Aplus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .pos then 1 else 0
def Aminus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .neg then -1 else 0
def B {n} (A : Pattern n) (i j : Fin n) : ℤ := Aplus A i j - Aminus A j i

theorem representative_sign (s : Sign) :
    (representative s = 0 ↔ s = .zero) ∧
    (0 < representative s ↔ s = .pos) ∧
    (representative s < 0 ↔ s = .neg) := by cases s <;> decide

theorem B_support {n} (A : Pattern n) (i j : Fin n) :
    B A i j ≠ 0 ↔ A i j = .pos ∨ A j i = .neg := by
  cases h : A i j <;> cases h' : A j i <;> simp [B,Aplus,Aminus,h,h']

def AP {n} (A : Pattern n) : Prop :=
  Irreducible (support A) ∧ (∀ i, ∃ j, A i j = .pos) ∧
    (∀ j, ∃ i, A i j = .pos) ∧ Irreducible (fun i j => B A i j ≠ 0)
def erase {n} (A : Pattern n) (r c : Fin n) : Pattern n :=
  fun i j => if i=r ∧ j=c then .zero else A i j
def MinimalAP {n} (A : Pattern n) := AP A ∧ ∀ r c, support A r c → ¬ AP (erase A r c)
def ZeroDiagonal {n} (A : Pattern n) := ∀ i, A i i = .zero
instance {n} (A : Pattern n) (i j : Fin n) : Decidable (support A i j) := inferInstanceAs (Decidable (A i j ≠ .zero))

def nnz {n} (A : Pattern n) := (Finset.univ.filter (fun p : Fin n × Fin n => support A p.1 p.2)).card

theorem irred_cut {n} (R : Fin n → Fin n → Prop) :
    Irreducible R ↔ ¬ CutReducible R := not_congr (block_cut R)
end APRefutation
```

<!-- LEAN-FILE Witness.lean SHA256 69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31 -->
```lean
import Source
namespace APRefutation
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def A : Pattern 5 := fun i j =>
  if (i,j) ∈ ([(0,4),(1,3),(2,1),(3,1),(4,0),(4,2)] : List (Fin 5 × Fin 5)) then .pos
  else if (i,j) ∈ ([(1,2),(2,4),(4,1)] : List (Fin 5 × Fin 5)) then .neg else .zero

instance {n} (R : Fin n → Fin n → Prop) [DecidableRel R] : Decidable (CutReducible R) := by
  unfold CutReducible
  infer_instance

def FiniteAP {n} (X : Pattern n) :=
  (¬ CutReducible (support X)) ∧ (∀ i, ∃ j, X i j = .pos) ∧
    (∀ j, ∃ i, X i j = .pos) ∧ ¬ CutReducible (fun i j => B X i j ≠ 0)
instance {n} (X : Pattern n) : Decidable (FiniteAP X) := by
  unfold FiniteAP
  infer_instance

theorem finiteAP_iff {n} (X : Pattern n) : FiniteAP X ↔ AP X := by
  simp only [FiniteAP, AP, irred_cut]

theorem actual_AP : AP A := finiteAP_iff A |>.mp (by decide)

theorem all_deletions : ∀ r c, support A r c → ¬ FiniteAP (erase A r c) := by decide

theorem actual_minimal : MinimalAP A := by
  refine ⟨actual_AP, ?_⟩
  intro r c h he
  exact all_deletions r c h ((finiteAP_iff _).mpr he)

theorem actual_diagonal : ZeroDiagonal A := by unfold ZeroDiagonal; decide
theorem actual_nnz : nnz A = 9 := by decide
theorem overlap_weights : B A 2 1 = 2 ∧ B A 4 2 = 2 := by decide

theorem witness : ∃ X : Pattern 5, MinimalAP X ∧ ZeroDiagonal X ∧ nnz X = 9 ∧ nnz X > 2*5-2 := by
  exact ⟨A,actual_minimal,actual_diagonal,actual_nnz,by rw [actual_nnz]; decide⟩

def SourceAssertion : Prop := ∀ n : ℕ, 0 < n → ∀ X : Pattern n,
  MinimalAP X → ZeroDiagonal X → nnz X ≤ 2*n-2

theorem refutation : ¬ SourceAssertion := by
  intro h
  have bad := h 5 (by decide) A actual_minimal actual_diagonal
  rw [actual_nnz] at bad
  exact (by decide : ¬ (9 ≤ 2*5-2)) bad
#print axioms witness
#print axioms refutation
#print axioms block_cut
#print axioms block_permutation
end APRefutation
```

<!-- LEAN-FILE Audit.lean SHA256 cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648 -->
```lean
import Witness
namespace APRefutation
-- Independent statement with every custom predicate expanded literally.
theorem expanded_refutation : ¬ (∀ n : ℕ, 0 < n → ∀ X : Fin n → Fin n → Sign,
  (((¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((X) (e (.inl i)) (e (.inr j)) ≠ Sign.zero)) ∧ (∀ i, ∃ j, (X) i j = Sign.pos) ∧ (∀ j, ∃ i, (X) i j = Sign.pos) ∧ (¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((if (X) (e (.inl i)) (e (.inr j)) = Sign.pos then (1 : ℤ) else 0) - (if (X) (e (.inr j)) (e (.inl i)) = Sign.neg then -1 else 0) ≠ 0))) ∧ ∀ r c, X r c ≠ Sign.zero → ¬ ((¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inl i)) (e (.inr j)) ≠ Sign.zero)) ∧ (∀ i, ∃ j, (fun i j => if i=r ∧ j=c then Sign.zero else X i j) i j = Sign.pos) ∧ (∀ j, ∃ i, (fun i j => if i=r ∧ j=c then Sign.zero else X i j) i j = Sign.pos) ∧ (¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((if (fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inl i)) (e (.inr j)) = Sign.pos then (1 : ℤ) else 0) - (if (fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inr j)) (e (.inl i)) = Sign.neg then -1 else 0) ≠ 0)))) →
  (∀ i, X i i = Sign.zero) →
  (Finset.univ.filter (fun p : Fin n × Fin n => X p.1 p.2 ≠ Sign.zero)).card ≤ 2*n-2) := by
  exact refutation
#print axioms expanded_refutation
#print axioms actual_AP
#print axioms all_deletions
#print axioms actual_nnz
#print axioms overlap_weights
#print axioms representative_sign
#print axioms B_support
end APRefutation
```

The extraction algorithm (standard Python only) is:

```python
import re, hashlib
from pathlib import Path
paper = Path("PAPER-v1.md").read_text()
blocks = re.findall(r"<!-- LEAN-FILE (\w+\.lean) SHA256 ([0-9a-f]{64}) -->\n```lean\n(.*?)```\n", paper, re.S)
assert [n for n, _, _ in blocks] == ["Source.lean", "Witness.lean", "Audit.lean"]
Path("src").mkdir(exist_ok=True)
for name, expected, text in blocks:
    raw = text.encode("utf-8")
    assert hashlib.sha256(raw).hexdigest() == expected
    Path("src", name).write_bytes(raw)
```

For an independent rebuild, create an EMPTY build directory. Set LEAN_PATH to that directory followed by ONLY the eight upstream_lean_paths in the pin object, separated by colons. Set LEAN_NUM_THREADS=1. For each module NAME in Source,Witness,Audit order, run the pinned lean executable with `-j1 -M3500 -DwarningAsError=true -o build/NAME.olean src/NAME.lean`, then separately run the pinned leanchecker executable with argument NAME and the same LEAN_PATH. These are the exact inner commands used by the frozen wrappers. The permitted lane execution uses `taskset -c 4,5 bash ./check32.sh NAME UNIQUE_LABEL` and `taskset -c 4,5 bash ./checker32.sh NAME UNIQUE_LABEL`. Each invocation has CPU115s, deadline130s, AS32GiB, sampled real-memory6GiB, two cores, and no parallel Lean jobs. The documentary runner has AS6GiB. This paragraph supplies reproduction instructions, not authority to bypass wrappers in this lane.

The fixed witness computations cover 25 positions, nine supported erasures and 32 Boolean subsets per cut test. No enumeration of 3^25 sign patterns occurs. All finite facts use ordinary kernel `decide`; source semantic bridges are general proofs. The endpoint audit explicitly expands all custom predicates, and the full transitive axiom printouts are preserved below.

## Formal invocation receipts and failures

Every formal wrapper invocation, including failures, is reproduced here with its full receipt and complete stdout. These are original bounded-run records, not evidence of independent review. A failed elaboration may print sorryAx from Lean's error recovery; no failed module was accepted or kernel-checked as production. The corresponding failed source versions are retained in drafts/. Only the final successful sources appear in the literal appendix above.

Total formal invocations represented: 16/64. Failures: 4. This includes compilation and separate kernel checking; versions/probes outside these calls: zero.

### f01-source

```json
{
  "utc": "2026-11-15T17:38:47.654459+00:00",
  "name": "f01-source",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.8867350190412253,
  "sampled_group_rss_peak_bytes": 1666854912,
  "sampled_max_process_vmpeak_bytes": 7460892672,
  "samples": 10,
  "exit": 1,
  "killed": null,
  "child_cpu_cumulative_s": 0.882369,
  "stderr": ""
}
```

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:10:24: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  @Membership.mem ?m.6 (Finset ?m.6) SetLike.instMembership { val := ?m.8, nodup := ?m.9 } ?m.7
in the target expression
  @Membership.mem Sign (Finset Sign) SetLike.instMembership { val := ↑Sign.enumList, nodup := Sign.enumList_nodup } x✝

x✝ : Sign
⊢ x✝ ∈ { val := ↑Sign.enumList, nodup := Sign.enumList_nodup }

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    Sign.enumList_nodup
  has type
    Sign.enumList.Nodup
  but is expected to have type
    (↑Sign.enumList).Nodup
  in the application
    { val := ↑Sign.enumList, nodup := Sign.enumList_nodup }
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:43:4: error: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:44:4: error: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:53:6: error: Type mismatch: After simplification, term
  this
 has type
  True
but is expected to have type
  s (e (Sum.inr j)) = false
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:93:32: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  DecidablePred fun p => support A p.1 p.2

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:93:32: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Fintype (Fin n × Fin n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
{"stage": "compile", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Source.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean"], "exit": 1, "source_sha256_before": "024e1dc3cfcbb5fc5f98644e93e3848bb549d173162529e852060ef636e5e6a8", "source_sha256_after": "024e1dc3cfcbb5fc5f98644e93e3848bb549d173162529e852060ef636e5e6a8", "olean_sha256_before": null, "olean_sha256_after": null, "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f02-source

```json
{
  "utc": "2026-11-15T17:39:06.621156+00:00",
  "name": "f02-source",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.8998249239521101,
  "sampled_group_rss_peak_bytes": 1659957248,
  "sampled_max_process_vmpeak_bytes": 7460757504,
  "samples": 10,
  "exit": 1,
  "killed": null,
  "child_cpu_cumulative_s": 0.897532,
  "stderr": ""
}
```

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean:97:32: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Fintype (Fin n × Fin n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
{"stage": "compile", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Source.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean"], "exit": 1, "source_sha256_before": "1c67d0c844a9c225a200d7b7f84191b3337f07569f22ed0a8e5586a676b6fd90", "source_sha256_after": "1c67d0c844a9c225a200d7b7f84191b3337f07569f22ed0a8e5586a676b6fd90", "olean_sha256_before": null, "olean_sha256_after": null, "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f03-source

```json
{
  "utc": "2026-11-15T17:39:21.259392+00:00",
  "name": "f03-source",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.916863891063258,
  "sampled_group_rss_peak_bytes": 1696014336,
  "sampled_max_process_vmpeak_bytes": 7497474048,
  "samples": 11,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 0.9047329999999999,
  "stderr": ""
}
```

```text
{"stage": "compile", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Source.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean"], "exit": 0, "source_sha256_before": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "source_sha256_after": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "olean_sha256_before": null, "olean_sha256_after": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f04-source-kernel

```json
{
  "utc": "2026-11-15T17:39:25.501062+00:00",
  "name": "f04-source-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.2371312759350985,
  "sampled_group_rss_peak_bytes": 1435471872,
  "sampled_max_process_vmpeak_bytes": 6433636352,
  "samples": 14,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.232793,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Source"], "exit": 0, "source_sha256_before": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "source_sha256_after": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "olean_sha256_before": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "olean_sha256_after": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f05-witness

```json
{
  "utc": "2026-11-15T17:39:48.165155+00:00",
  "name": "f05-witness",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.7582111939555034,
  "sampled_group_rss_peak_bytes": 1792679936,
  "sampled_max_process_vmpeak_bytes": 7497797632,
  "samples": 20,
  "exit": 1,
  "killed": null,
  "child_cpu_cumulative_s": 1.7507129999999997,
  "stderr": ""
}
```

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Witness.lean:33:47: error: failed to synthesize
  Decidable (ZeroDiagonal A)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
'APRefutation.witness' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'APRefutation.refutation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'APRefutation.block_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.block_permutation' depends on axioms: [propext, Quot.sound]
{"stage": "compile", "module": "Witness", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Witness.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Witness.lean"], "exit": 1, "source_sha256_before": "1caca5fc756ede6d6d825bfa18d7017e3e065e4ae083f1e84ce4e44c8fda65d7", "source_sha256_after": "1caca5fc756ede6d6d825bfa18d7017e3e065e4ae083f1e84ce4e44c8fda65d7", "olean_sha256_before": null, "olean_sha256_after": null, "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f06-witness

```json
{
  "utc": "2026-11-15T17:40:15.998322+00:00",
  "name": "f06-witness",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.859204300912097,
  "sampled_group_rss_peak_bytes": 1792606208,
  "sampled_max_process_vmpeak_bytes": 7497797632,
  "samples": 20,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.8405110000000002,
  "stderr": ""
}
```

```text
'APRefutation.witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.block_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.block_permutation' depends on axioms: [propext, Quot.sound]
{"stage": "compile", "module": "Witness", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Witness.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Witness.lean"], "exit": 0, "source_sha256_before": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "source_sha256_after": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "olean_sha256_before": null, "olean_sha256_after": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f07-audit

```json
{
  "utc": "2026-11-15T17:40:39.267309+00:00",
  "name": "f07-audit",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.77815135801211,
  "sampled_group_rss_peak_bytes": 1689174016,
  "sampled_max_process_vmpeak_bytes": 7497949184,
  "samples": 9,
  "exit": 1,
  "killed": null,
  "child_cpu_cumulative_s": 0.774934,
  "stderr": ""
}
```

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Audit.lean:8:2: error: Type mismatch: After simplification, term
  refutation
 has type
  Not
    (∀ (n : ℕ),
      0 < n →
        ∀ (X : Pattern n),
          (((¬∃ k l, 0 < k ∧ 0 < l ∧ ∃ e, ∀ (i : Fin k) (j : Fin l), ¬X (e (Sum.inl i)) (e (Sum.inr j)) ≠ Sign.zero) ∧
                (∀ (i : Fin n), ∃ j, X i j = Sign.pos) ∧
                  (∀ (j : Fin n), ∃ i, X i j = Sign.pos) ∧
                    ¬∃ k l,
                        0 < k ∧
                          0 < l ∧
                            ∃ e,
                              ∀ (i : Fin k) (j : Fin l),
                                ¬((if X (e (Sum.inl i)) (e (Sum.inr j)) = Sign.pos then 1 else 0) -
                                      if X (e (Sum.inr j)) (e (Sum.inl i)) = Sign.neg then -1 else 0) ≠
                                    0) ∧
              ∀ (r c : Fin n),
                X r c ≠ Sign.zero →
                  ¬((¬∃ k l,
                          0 < k ∧
                            0 < l ∧
                              ∃ e,
                                ∀ (i : Fin k) (j : Fin l),
                                  ¬(if e (Sum.inl i) = r ∧ e (Sum.inr j) = c then Sign.zero
                                      else X (e (Sum.inl i)) (e (Sum.inr j))) ≠
                                      Sign.zero) ∧
                      (∀ (i : Fin n), ∃ j, (if i = r ∧ j = c then Sign.zero else X i j) = Sign.pos) ∧
                        (∀ (j : Fin n), ∃ i, (if i = r ∧ j = c then Sign.zero else X i j) = Sign.pos) ∧
                          ¬∃ k l,
                              0 < k ∧
                                0 < l ∧
                                  ∃ e,
                                    ∀ (i : Fin k) (j : Fin l),
                                      ¬((if
                                                (if e (Sum.inl i) = r ∧ e (Sum.inr j) = c then Sign.zero
                                                  else X (e (Sum.inl i)) (e (Sum.inr j))) =
                                                  Sign.pos then
                                              1
                                            else 0) -
                                            if
                                                (if e (Sum.inr j) = r ∧ e (Sum.inl i) = c then Sign.zero
                                                  else X (e (Sum.inr j)) (e (Sum.inl i))) =
                                                  Sign.neg then
                                              -1
                                            else 0) ≠
                                          0)) →
            (∀ (i : Fin n), X i i = Sign.zero) → {p | X p.1 p.2 ≠ Sign.zero}.card ≤ 2 * n - 2)
but is expected to have type
  Not
    (∀ (n : ℕ),
      0 < n →
        ∀ (X : Fin n → Fin n → Sign),
          (((¬∃ k l, 0 < k ∧ 0 < l ∧ ∃ e, ∀ (i : Fin k) (j : Fin l), ¬X (e (Sum.inl i)) (e (Sum.inr j)) ≠ Sign.zero) ∧
                (∀ (i : Fin n), ∃ j, X i j = Sign.pos) ∧
                  (∀ (j : Fin n), ∃ i, X i j = Sign.pos) ∧
                    ¬∃ k l,
                        0 < k ∧
                          0 < l ∧
                            ∃ e,
                              ∀ (i : Fin k) (j : Fin l),
                                ¬((if X (e (Sum.inl i)) (e (Sum.inr j)) = Sign.pos then 1 else 0) -
                                      if X (e (Sum.inr j)) (e (Sum.inl i)) = Sign.neg then -1 else 0) ≠
                                    0) ∧
              ∀ (r c : Fin n),
                X r c ≠ Sign.zero →
                  ¬((¬∃ k l,
                          0 < k ∧
                            0 < l ∧
                              ∃ e,
                                ∀ (i : Fin k) (j : Fin l),
                                  ¬(if e (Sum.inl i) = r ∧ e (Sum.inr j) = c then Sign.zero
                                      else X (e (Sum.inl i)) (e (Sum.inr j))) ≠
                                      Sign.zero) ∧
                      (∀ (i : Fin n), ∃ j, (if i = r ∧ j = c then Sign.zero else X i j) = Sign.pos) ∧
                        (∀ (j : Fin n), ∃ i, (if i = r ∧ j = c then Sign.zero else X i j) = Sign.pos) ∧
                          ¬∃ k l,
                              0 < k ∧
                                0 < l ∧
                                  ∃ e,
                                    ∀ (i : Fin k) (j : Fin l),
                                      ¬((if
                                                (if e (Sum.inl i) = r ∧ e (Sum.inr j) = c then Sign.zero
                                                  else X (e (Sum.inl i)) (e (Sum.inr j))) =
                                                  Sign.pos then
                                              1
                                            else 0) -
                                            if
                                                (if e (Sum.inr j) = r ∧ e (Sum.inl i) = c then Sign.zero
                                                  else X (e (Sum.inr j)) (e (Sum.inl i))) =
                                                  Sign.neg then
                                              -1
                                            else 0) ≠
                                          0)) →
            (∀ (i : Fin n), X i i = Sign.zero) → {p | X p.1 p.2 ≠ Sign.zero}.card ≤ 2 * n - 2)
'APRefutation.expanded_refutation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'APRefutation.actual_AP' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.all_deletions' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.actual_nnz' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.overlap_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.representative_sign' does not depend on any axioms
'APRefutation.B_support' depends on axioms: [propext, Classical.choice, Quot.sound]
{"stage": "compile", "module": "Audit", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Audit.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Audit.lean"], "exit": 1, "source_sha256_before": "b263171576a886b1713906561571e8c1552133e34982afd3a2b1059d574d5af5", "source_sha256_after": "b263171576a886b1713906561571e8c1552133e34982afd3a2b1059d574d5af5", "olean_sha256_before": null, "olean_sha256_after": null, "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f08-audit

```json
{
  "utc": "2026-11-15T17:40:51.534402+00:00",
  "name": "f08-audit",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.7401726150419563,
  "sampled_group_rss_peak_bytes": 1674948608,
  "sampled_max_process_vmpeak_bytes": 6449377280,
  "samples": 8,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 0.736439,
  "stderr": ""
}
```

```text
'APRefutation.expanded_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.actual_AP' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.all_deletions' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.actual_nnz' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.overlap_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.representative_sign' does not depend on any axioms
'APRefutation.B_support' depends on axioms: [propext, Classical.choice, Quot.sound]
{"stage": "compile", "module": "Audit", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Audit.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Audit.lean"], "exit": 0, "source_sha256_before": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "source_sha256_after": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "olean_sha256_before": null, "olean_sha256_after": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f09-witness-kernel

```json
{
  "utc": "2026-11-15T17:40:56.874666+00:00",
  "name": "f09-witness-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.6778904909733683,
  "sampled_group_rss_peak_bytes": 1532260352,
  "sampled_max_process_vmpeak_bytes": 6433853440,
  "samples": 18,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.595181,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Witness", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Witness"], "exit": 0, "source_sha256_before": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "source_sha256_after": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "olean_sha256_before": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "olean_sha256_after": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f10-audit-kernel

```json
{
  "utc": "2026-11-15T17:41:11.365560+00:00",
  "name": "f10-audit-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.2124839019961655,
  "sampled_group_rss_peak_bytes": 1435660288,
  "sampled_max_process_vmpeak_bytes": 6433816576,
  "samples": 14,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.1934770000000001,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Audit", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Audit"], "exit": 0, "source_sha256_before": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "source_sha256_after": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "olean_sha256_before": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "olean_sha256_after": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f11-extracted-source

```json
{
  "utc": "2026-11-15T17:44:22.999864+00:00",
  "name": "f11-extracted-source",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.9458628600696102,
  "sampled_group_rss_peak_bytes": 1701593088,
  "sampled_max_process_vmpeak_bytes": 7497707520,
  "samples": 11,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 0.939956,
  "stderr": ""
}
```

```text
{"stage": "compile", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Source.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Source.lean"], "exit": 0, "source_sha256_before": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "source_sha256_after": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "olean_sha256_before": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "olean_sha256_after": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f12-extracted-source-kernel

```json
{
  "utc": "2026-11-15T17:44:45.955526+00:00",
  "name": "f12-extracted-source-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.21580281003844,
  "sampled_group_rss_peak_bytes": 1435549696,
  "sampled_max_process_vmpeak_bytes": 6433636352,
  "samples": 14,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.208786,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Source", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Source"], "exit": 0, "source_sha256_before": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "source_sha256_after": "2ebabbd6429fcfd0e5db8c32bec6e8af0cc71433482900bce6dc717ec9c808a6", "olean_sha256_before": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "olean_sha256_after": "9732c157bbe3b0b75d9081d4334a921449b648948257a67a92c25f66564773a6", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f13-extracted-witness

```json
{
  "utc": "2026-11-15T17:45:08.494498+00:00",
  "name": "f13-extracted-witness",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.7427059959154576,
  "sampled_group_rss_peak_bytes": 1793134592,
  "sampled_max_process_vmpeak_bytes": 7497797632,
  "samples": 20,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.736421,
  "stderr": ""
}
```

```text
'APRefutation.witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.block_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.block_permutation' depends on axioms: [propext, Quot.sound]
{"stage": "compile", "module": "Witness", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Witness.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Witness.lean"], "exit": 0, "source_sha256_before": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "source_sha256_after": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "olean_sha256_before": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "olean_sha256_after": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f14-extracted-witness-kernel

```json
{
  "utc": "2026-11-15T17:45:29.557688+00:00",
  "name": "f14-extracted-witness-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.5989654069999233,
  "sampled_group_rss_peak_bytes": 1534361600,
  "sampled_max_process_vmpeak_bytes": 6433787904,
  "samples": 18,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.593442,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Witness", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Witness"], "exit": 0, "source_sha256_before": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "source_sha256_after": "69ec2ac737661f7d3c079ad768a49d6eeec4955c575a5699b16d607615e64e31", "olean_sha256_before": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "olean_sha256_after": "1da7fb94ff4ef3c2d162497137778aaf7cb193fc1b817b5c9dfe1de24c606748", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f15-extracted-audit

```json
{
  "utc": "2026-11-15T17:45:44.130613+00:00",
  "name": "f15-extracted-audit",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 0.7207431429997087,
  "sampled_group_rss_peak_bytes": 1674362880,
  "sampled_max_process_vmpeak_bytes": 6449377280,
  "samples": 8,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 0.7178789999999999,
  "stderr": ""
}
```

```text
'APRefutation.expanded_refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.actual_AP' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.all_deletions' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.actual_nnz' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.overlap_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'APRefutation.representative_sign' does not depend on any axioms
'APRefutation.B_support' depends on axioms: [propext, Classical.choice, Quot.sound]
{"stage": "compile", "module": "Audit", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean", "-j1", "-M3500", "-DwarningAsError=true", "-o", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build/Audit.olean", "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/src/Audit.lean"], "exit": 0, "source_sha256_before": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "source_sha256_after": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "olean_sha256_before": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "olean_sha256_after": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

### f16-extracted-audit-kernel

```json
{
  "utc": "2026-11-15T17:45:44.947472+00:00",
  "name": "f16-extracted-audit-kernel",
  "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1",
  "command": [
    "/usr/bin/python3",
    "-I",
    "-B",
    "-c",
    "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
  ],
  "env_overrides": {
    "MALLOC_ARENA_MAX": "2"
  },
  "affinity": [
    4,
    5
  ],
  "cpu_limit_s": 115,
  "as_limit_bytes": 34359738368,
  "group_rss_guard_bytes": 6442450944,
  "deadline_s": 130,
  "wall_s": 1.1977083629462868,
  "sampled_group_rss_peak_bytes": 1435590656,
  "sampled_max_process_vmpeak_bytes": 6433816576,
  "samples": 14,
  "exit": 0,
  "killed": null,
  "child_cpu_cumulative_s": 1.189098,
  "stderr": ""
}
```

```text
{"stage": "check", "module": "Audit", "argv": ["/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker", "Audit"], "exit": 0, "source_sha256_before": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "source_sha256_after": "cc02f5b2fc4a9b7960a74ac038c8a08105fe6a937f1ba6ef63f94659eba5b648", "olean_sha256_before": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "olean_sha256_after": "3f13f864dec0b2637033962ef574dfe09625771acdf69458b9f1f79b514ce629", "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ap-minimal-sparsity-refutation-formal-sol-r1/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean", "LEAN_NUM_THREADS": 1}

```

## Primary source inventory

Read on 2026-11-15: exact raw MathDB target; v3 text sections at sign/digraph definitions, Section 3 definitions and Conjectures 5.1/5.2; rendered source pages10,12,22; supplied source identity and root intake; supplied independent gates and selected report sections, not its complete body. Target source URLs: https://mathdb.com/p/352795/the-sparsity-conjecture-for-minimally-ap-irreducible-sign-pa and https://arxiv.org/abs/2112.00442v3 . No fresh HTTP request was made. The following physical input hashes specify the copies, not claims of complete personal reading. Other owned release fields and coverage bundles remain supplied evidence.

- inputs/mathdb-352795.raw.jsonl: 1827 bytes; SHA256 d9f0fb711155d9d9a6b2101765b30966bd76979a38be8ab0c966749b1efa79a3.
- inputs/2112.00442v3.txt: 153593 bytes; SHA256 a29482c3443e4d18f5f3ce112e579c0f19368d0f4cda897344b61d93671f53ab.
- inputs/2112.00442v3.pdf: 261150 bytes; SHA256 c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379.
- inputs/SOURCE-IDENTITY-CARD.json: 510 bytes; SHA256 1a5e0ef1a069b59b2eac4f082f924c61ad402e3ad13c2c4f5ad002ef8a4853ca.
- inputs/independent-gates-v2.json: 890 bytes; SHA256 8a8625b74b49d29bb9e6144d5835b1b553b9e1daab41abe2dfc88c5104370c36.
- inputs/ap-minimal-sparsity-independent-pass-formal-go-root-intake-20261115-v1.json: 2071 bytes; SHA256 9859a7922d9edfd6d640eb3391dc29958e14f32c8450623b2032cc8fe84c3a26.

## Standard dependency revisions

- plausible: 118aa17ee84656b8bd727fef7c458ee8c833385c.
- LeanSearchClient: ddf04cf3949fa556442341e87d47f9f6e6074707.
- importGraph: e928b72544873815af278d38681b31c0293588e3.
- proofwidgets: 106ff4fafc74ef4ac99d81dbf3ab399118f497a5.
- aesop: 355695d523e41d0554926416cba2a2b3544fbbc9.
- Qq: 6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259.
- batteries: f2effa3d803fda822b1f97b806c47cf2adfbcbc2.
The manifest also lists inherited Cli metadata; Cli is not added to the eight-package LEAN_PATH and is not an authorized project dependency here.

## Retained unsuccessful source drafts

These are historical failures, not production modules and not extraction targets.

### drafts/Audit-f07.lean (SHA256 b263171576a886b1713906561571e8c1552133e34982afd3a2b1059d574d5af5)

```lean
import Witness
namespace APRefutation
-- Independent statement with every custom predicate expanded literally.
theorem expanded_refutation : ¬ (∀ n : ℕ, 0 < n → ∀ X : Fin n → Fin n → Sign,
  (((¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((X) (e (.inl i)) (e (.inr j)) ≠ Sign.zero)) ∧ (∀ i, ∃ j, (X) i j = Sign.pos) ∧ (∀ j, ∃ i, (X) i j = Sign.pos) ∧ (¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((if (X) (e (.inl i)) (e (.inr j)) = Sign.pos then (1 : ℤ) else 0) - (if (X) (e (.inr j)) (e (.inl i)) = Sign.neg then -1 else 0) ≠ 0))) ∧ ∀ r c, X r c ≠ Sign.zero → ¬ ((¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inl i)) (e (.inr j)) ≠ Sign.zero)) ∧ (∀ i, ∃ j, (fun i j => if i=r ∧ j=c then Sign.zero else X i j) i j = Sign.pos) ∧ (∀ j, ∃ i, (fun i j => if i=r ∧ j=c then Sign.zero else X i j) i j = Sign.pos) ∧ (¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n, ∀ i j, ¬ ((if (fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inl i)) (e (.inr j)) = Sign.pos then (1 : ℤ) else 0) - (if (fun i j => if i=r ∧ j=c then Sign.zero else X i j) (e (.inr j)) (e (.inl i)) = Sign.neg then -1 else 0) ≠ 0)))) →
  (∀ i, X i i = Sign.zero) →
  (Finset.univ.filter (fun p : Fin n × Fin n => X p.1 p.2 ≠ Sign.zero)).card ≤ 2*n-2) := by
  simpa only [SourceAssertion, MinimalAP, AP, Irreducible, BlockReducible,
    support, erase, ZeroDiagonal, nnz, B, Aplus, Aminus] using refutation
#print axioms expanded_refutation
#print axioms actual_AP
#print axioms all_deletions
#print axioms actual_nnz
#print axioms overlap_weights
#print axioms representative_sign
#print axioms B_support
end APRefutation
```

### drafts/Source-f01.lean (SHA256 024e1dc3cfcbb5fc5f98644e93e3848bb549d173162529e852060ef636e5e6a8)

```lean
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

namespace APRefutation
inductive Sign where
  | zero | pos | neg
  deriving DecidableEq, Fintype
abbrev Pattern (n : ℕ) := Fin n → Fin n → Sign
def support {n} (A : Pattern n) (i j : Fin n) : Prop := A i j ≠ .zero
-- An ordered two-block decomposition: equivalently a simultaneous permutation.
def BlockReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n,
    ∀ i j, ¬ R (e (.inl i)) (e (.inr j))
def CutReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ s : Fin n → Bool, (∃ i, s i = true) ∧ (∃ j, s j = false) ∧
    ∀ i j, s i = true → s j = false → ¬ R i j

theorem block_cut {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ CutReducible R := by
  classical
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    let s : Fin n → Bool := fun x => (e.symm x).isLeft
    refine ⟨s, ⟨e (.inl ⟨0,hk⟩), ?_⟩, ⟨e (.inr ⟨0,hl⟩), ?_⟩, ?_⟩
    · simp [s]
    · simp [s]
    · intro i j hi hj
      obtain ⟨x, rfl⟩ := e.surjective i
      obtain ⟨y, rfl⟩ := e.surjective j
      cases x with
      | inl a =>
        cases y with
        | inl b => simp [s] at hj
        | inr b => exact h a b
      | inr a => simp [s] at hi
  · rintro ⟨s,⟨a,ha⟩,⟨b,hb⟩,h⟩
    let S : Set (Fin n) := {x | s x = true}
    let T : Set (Fin n) := Sᶜ
    have hb' : b ∈ T := by simp [T,S,hb]
    letI : Nonempty S := ⟨⟨a,ha⟩⟩
    letI : Nonempty T := ⟨⟨b,hb'⟩⟩
    let e := (Equiv.sumCongr (Fintype.equivFin S).symm
      (Fintype.equivFin T).symm).trans (Equiv.Set.sumCompl S)
    refine ⟨Fintype.card S, Fintype.card T, Fintype.card_pos,
      Fintype.card_pos, e, ?_⟩
    intro i j
    apply h
    · exact ((Fintype.equivFin S).symm i).property
    · have := ((Fintype.equivFin T).symm j).property
      simpa [T,S, Bool.not_eq_true] using this

-- Literal contiguous zero block after a simultaneous permutation of the indices.
theorem block_permutation {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      ∃ e : Fin (k+l) ≃ Fin n,
        ∀ i : Fin k, ∀ j : Fin l, ¬ R (e (Fin.castAdd l i)) (e (Fin.natAdd k j)) := by
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.symm.trans e,by simpa using h⟩
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.trans e,by simpa using h⟩

theorem block_order {n k l} (e : Fin (k+l) ≃ Fin n) : k+l=n := by
  simpa using Fintype.card_congr e

def Irreducible {n} (R : Fin n → Fin n → Prop) := ¬ BlockReducible R

def representative : Sign → ℤ
  | .zero => 0 | .pos => 1 | .neg => -1
def Aplus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .pos then 1 else 0
def Aminus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .neg then -1 else 0
def B {n} (A : Pattern n) (i j : Fin n) : ℤ := Aplus A i j - Aminus A j i

theorem representative_sign (s : Sign) :
    (representative s = 0 ↔ s = .zero) ∧
    (0 < representative s ↔ s = .pos) ∧
    (representative s < 0 ↔ s = .neg) := by cases s <;> decide

theorem B_support {n} (A : Pattern n) (i j : Fin n) :
    B A i j ≠ 0 ↔ A i j = .pos ∨ A j i = .neg := by
  cases h : A i j <;> cases h' : A j i <;> simp [B,Aplus,Aminus,h,h']

def AP {n} (A : Pattern n) : Prop :=
  Irreducible (support A) ∧ (∀ i, ∃ j, A i j = .pos) ∧
    (∀ j, ∃ i, A i j = .pos) ∧ Irreducible (fun i j => B A i j ≠ 0)
def erase {n} (A : Pattern n) (r c : Fin n) : Pattern n :=
  fun i j => if i=r ∧ j=c then .zero else A i j
def MinimalAP {n} (A : Pattern n) := AP A ∧ ∀ r c, support A r c → ¬ AP (erase A r c)
def ZeroDiagonal {n} (A : Pattern n) := ∀ i, A i i = .zero
def nnz {n} (A : Pattern n) := (Finset.univ.filter (fun p : Fin n × Fin n => support A p.1 p.2)).card

theorem irred_cut {n} (R : Fin n → Fin n → Prop) :
    Irreducible R ↔ ¬ CutReducible R := not_congr (block_cut R)
end APRefutation
```

### drafts/Source-f02.lean (SHA256 1c67d0c844a9c225a200d7b7f84191b3337f07569f22ed0a8e5586a676b6fd90)

```lean
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

namespace APRefutation
inductive Sign where
  | zero | pos | neg
  deriving DecidableEq
abbrev Pattern (n : ℕ) := Fin n → Fin n → Sign
def support {n} (A : Pattern n) (i j : Fin n) : Prop := A i j ≠ .zero
-- An ordered two-block decomposition: equivalently a simultaneous permutation.
def BlockReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ e : Fin k ⊕ Fin l ≃ Fin n,
    ∀ i j, ¬ R (e (.inl i)) (e (.inr j))
def CutReducible {n} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ s : Fin n → Bool, (∃ i, s i = true) ∧ (∃ j, s j = false) ∧
    ∀ i j, s i = true → s j = false → ¬ R i j

theorem block_cut {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ CutReducible R := by
  classical
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    let s : Fin n → Bool := fun x => (e.symm x).isLeft
    refine ⟨s, ⟨e (.inl ⟨0,hk⟩), ?_⟩, ⟨e (.inr ⟨0,hl⟩), ?_⟩, ?_⟩
    · simp [s]
    · simp [s]
    · intro i j hi hj
      obtain ⟨x, rfl⟩ := e.surjective i
      obtain ⟨y, rfl⟩ := e.surjective j
      cases x with
      | inl a =>
        cases y with
        | inl b => simp [s] at hj
        | inr b => exact h a b
      | inr a => simp [s] at hi
  · rintro ⟨s,⟨a,ha⟩,⟨b,hb⟩,h⟩
    let S : Set (Fin n) := {x | s x = true}
    let T : Set (Fin n) := Sᶜ
    have hb' : b ∈ T := by simp [T,S,hb]
    let : Nonempty S := ⟨⟨a,ha⟩⟩
    let : Nonempty T := ⟨⟨b,hb'⟩⟩
    let e := (Equiv.sumCongr (Fintype.equivFin S).symm
      (Fintype.equivFin T).symm).trans (Equiv.Set.sumCompl S)
    refine ⟨Fintype.card S, Fintype.card T, Fintype.card_pos,
      Fintype.card_pos, e, ?_⟩
    intro i j
    apply h
    · exact ((Fintype.equivFin S).symm i).property
    · have := ((Fintype.equivFin T).symm j).property
      change s (↑((Fintype.equivFin T).symm j)) = false
      change s (↑((Fintype.equivFin T).symm j)) ≠ true at this
      cases hv : s (↑((Fintype.equivFin T).symm j)) <;> simp_all

-- Literal contiguous zero block after a simultaneous permutation of the indices.
theorem block_permutation {n} (R : Fin n → Fin n → Prop) :
    BlockReducible R ↔ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      ∃ e : Fin (k+l) ≃ Fin n,
        ∀ i : Fin k, ∀ j : Fin l, ¬ R (e (Fin.castAdd l i)) (e (Fin.natAdd k j)) := by
  constructor
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.symm.trans e,by simpa using h⟩
  · rintro ⟨k,l,hk,hl,e,h⟩
    exact ⟨k,l,hk,hl,finSumFinEquiv.trans e,by simpa using h⟩

theorem block_order {n k l} (e : Fin (k+l) ≃ Fin n) : k+l=n := by
  simpa using Fintype.card_congr e

def Irreducible {n} (R : Fin n → Fin n → Prop) := ¬ BlockReducible R

def representative : Sign → ℤ
  | .zero => 0 | .pos => 1 | .neg => -1
def Aplus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .pos then 1 else 0
def Aminus {n} (A : Pattern n) (i j : Fin n) : ℤ := if A i j = .neg then -1 else 0
def B {n} (A : Pattern n) (i j : Fin n) : ℤ := Aplus A i j - Aminus A j i

theorem representative_sign (s : Sign) :
    (representative s = 0 ↔ s = .zero) ∧
    (0 < representative s ↔ s = .pos) ∧
    (representative s < 0 ↔ s = .neg) := by cases s <;> decide

theorem B_support {n} (A : Pattern n) (i j : Fin n) :
    B A i j ≠ 0 ↔ A i j = .pos ∨ A j i = .neg := by
  cases h : A i j <;> cases h' : A j i <;> simp [B,Aplus,Aminus,h,h']

def AP {n} (A : Pattern n) : Prop :=
  Irreducible (support A) ∧ (∀ i, ∃ j, A i j = .pos) ∧
    (∀ j, ∃ i, A i j = .pos) ∧ Irreducible (fun i j => B A i j ≠ 0)
def erase {n} (A : Pattern n) (r c : Fin n) : Pattern n :=
  fun i j => if i=r ∧ j=c then .zero else A i j
def MinimalAP {n} (A : Pattern n) := AP A ∧ ∀ r c, support A r c → ¬ AP (erase A r c)
def ZeroDiagonal {n} (A : Pattern n) := ∀ i, A i i = .zero
instance {n} (A : Pattern n) (i j : Fin n) : Decidable (support A i j) := inferInstanceAs (Decidable (A i j ≠ .zero))

def nnz {n} (A : Pattern n) := (Finset.univ.filter (fun p : Fin n × Fin n => support A p.1 p.2)).card

theorem irred_cut {n} (R : Fin n → Fin n → Prop) :
    Irreducible R ↔ ¬ CutReducible R := not_congr (block_cut R)
end APRefutation
```

### drafts/Witness-f05.lean (SHA256 1caca5fc756ede6d6d825bfa18d7017e3e065e4ae083f1e84ce4e44c8fda65d7)

```lean
import Source
namespace APRefutation
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def A : Pattern 5 := fun i j =>
  if (i,j) ∈ ([(0,4),(1,3),(2,1),(3,1),(4,0),(4,2)] : List (Fin 5 × Fin 5)) then .pos
  else if (i,j) ∈ ([(1,2),(2,4),(4,1)] : List (Fin 5 × Fin 5)) then .neg else .zero

instance {n} (R : Fin n → Fin n → Prop) [DecidableRel R] : Decidable (CutReducible R) := by
  unfold CutReducible
  infer_instance

def FiniteAP {n} (X : Pattern n) :=
  (¬ CutReducible (support X)) ∧ (∀ i, ∃ j, X i j = .pos) ∧
    (∀ j, ∃ i, X i j = .pos) ∧ ¬ CutReducible (fun i j => B X i j ≠ 0)
instance {n} (X : Pattern n) : Decidable (FiniteAP X) := by
  unfold FiniteAP
  infer_instance

theorem finiteAP_iff {n} (X : Pattern n) : FiniteAP X ↔ AP X := by
  simp only [FiniteAP, AP, irred_cut]

theorem actual_AP : AP A := finiteAP_iff A |>.mp (by decide)

theorem all_deletions : ∀ r c, support A r c → ¬ FiniteAP (erase A r c) := by decide

theorem actual_minimal : MinimalAP A := by
  refine ⟨actual_AP, ?_⟩
  intro r c h he
  exact all_deletions r c h ((finiteAP_iff _).mpr he)

theorem actual_diagonal : ZeroDiagonal A := by decide
theorem actual_nnz : nnz A = 9 := by decide
theorem overlap_weights : B A 2 1 = 2 ∧ B A 4 2 = 2 := by decide

theorem witness : ∃ X : Pattern 5, MinimalAP X ∧ ZeroDiagonal X ∧ nnz X = 9 ∧ nnz X > 2*5-2 := by
  exact ⟨A,actual_minimal,actual_diagonal,actual_nnz,by rw [actual_nnz]; decide⟩

def SourceAssertion : Prop := ∀ n : ℕ, 0 < n → ∀ X : Pattern n,
  MinimalAP X → ZeroDiagonal X → nnz X ≤ 2*n-2

theorem refutation : ¬ SourceAssertion := by
  intro h
  have bad := h 5 (by decide) A actual_minimal actual_diagonal
  rw [actual_nnz] at bad
  exact (by decide : ¬ (9 ≤ 2*5-2)) bad
#print axioms witness
#print axioms refutation
#print axioms block_cut
#print axioms block_permutation
end APRefutation
```

