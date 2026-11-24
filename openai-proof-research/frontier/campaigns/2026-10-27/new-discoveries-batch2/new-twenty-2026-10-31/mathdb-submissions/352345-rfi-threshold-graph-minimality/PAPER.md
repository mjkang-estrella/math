# Minimality of the initial right-free-interval threshold graph

MathDB 352345. Manuscript and formal certificate, 2026-11-20.

## Abstract and verification status

We prove the source's same-depth minimality conjecture for the initial graph
produced by the Right Free Interval Algorithm, for every real N>0 and depth
r≥2. The proof uses literal adjacency matrices, explicit positive subspaces,
constructive suffix responses, and a consecutive-floor inequality. The exact
endpoint `RFIMinimality.conj_10_1` is formalized in Lean 4 with Mathlib using
only propext, Classical.choice and Quot.sound. The upper bound μ≤N is closed.
No acceptance, submission, or unrestricted novelty claim is made.

## The problem and its source

L. E. Allem, E. R. Oliveira and F. Tura, *On I-eigenvalue free threshold graphs*,
[arXiv:2110.12107](https://arxiv.org/abs/2110.12107), v1 (2021).
The journal version is *Generating I-eigenvalue free threshold graphs*,
*Electronic Journal of Combinatorics* **30**(2) (2023), P2.30,
[DOI 10.37236/11225](https://doi.org/10.37236/11225).
The journal Conjecture 29 is arXiv Conjecture 10.1.

The conjecture reads (journal p. 26, mathematical typesetting normalized):

> Conjecture 29. Let N > 0 and r ≥ 2 be fixed numbers defining the interval I =
> (0, N], and T_G(a₁, …, a_r), the initial threshold graph obtained from RFI(N, r),
> then G is minimal, i.e., if G̃ ≼ G is such that G̃ is also I-eigenvalue free then G̃ = G.

The MathDB record supplied to this lane states verbatim:

> Let $N>0$ and $r\geq 2$ be fixed, and let $I=(0,N]$. Let $T_G(a_1,\ldots,a_r)$ be the initial threshold graph obtained from RFI$(N,r)$. **Minimality conjecture.** The graph $G$ is minimal: if $\widetilde{G}\preceq G$ is also $I$-eigenvalue free, then $\widetilde{G}=G$. This conjecture asserts that no smaller threshold graph is $(0,N]$-eigenvalue free. The authors report exhaustive computational searches for several positive values of $N$ that found no smaller example, but the general claim remains open.

We use exactly the source's same-depth coordinatewise order. No comparison of
objects of different depths is asserted.

## Source definitions next to the Lean transcription

Quotations below come from the retained journal text in `evidence/source-journal.txt`;
line ranges identify extraction locations, and page numbers refer to the journal.
Subscripts, the floor symbols and the order symbol are typeset normally here.

### Graph, blocks, validity

Source §2, pp. 3–4 (extracted lines 110–160):

> More specifically, we may represent a threshold graph on n vertices using a binary
> sequence (b₁, b₂, …, b_n) as follows: b_i = 0 if vertex v_i is added as an isolated
> vertex, and b_i = 1 if v_i is added as a dominating vertex.

> The cotree denoted by T_G(a₁, a₂, …, a_r) with a_i ≥ 1 for 1 ≤ i ≤ r − 1,
> a_r ≥ 2 and r odd is depicted in Figure 2.

The binary representation printed immediately below Figure 2 is
`(1^{a_r}, b₂^{a_{r−1}}, …, b_{r−1}^{a₂}, 1^{a₁})` for odd r.
The cotree's root is a join; its interior types alternate. Thus source block i
is a clique exactly for odd i. For distinct blocks i<j, all their edges are
present exactly for odd i. For even r the deepest block is independent.
These rules imply the following literal sigma-type definition: min of the two
block indices is the earlier join/union node, and inequality of vertices
removes the loop. Equal block indices retain the same parity rule.

```lean
def Valid (r : ℕ) (b : Fin r → ℕ) : Prop :=
  (∀ i, 1 ≤ b i) ∧ ∀ h : 0 < r, 2 ≤ b ⟨r-1, by omega⟩

def TG (r : ℕ) (b : Fin r → ℕ) : SimpleGraph (Σ i : Fin r, Fin (b i)) where
  Adj x y := x ≠ y ∧ Odd ((min x.1 y.1 : Fin r).val + 1)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [min_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (r : ℕ) (b : Fin r → ℕ) : DecidableRel (TG r b).Adj :=
  fun _ _ => Classical.propDecidable _

def f (X Y : ℝ) : ℝ := (X*Y-1)/(X+Y-2)
def g (X Y : ℝ) : ℝ := X*Y/(X+Y)

/-- Real floor followed by Int.toNat, as required by the source transcription. -/
def greedy (t : ℝ) : ℕ := 1 + (Int.floor t).toNat

/-- d downward steps from the final block. Only d < r is used by rfiInitial. -/
def rfiState (N : ℝ) (r : ℕ) : ℕ → ℕ × ℝ
  | 0 => if Odd r then
      let a := greedy (N+1)
      (a, 1-(1+N)/a)
    else (2, -N/2)
  | d+1 =>
      let s := (rfiState N r d).2
      if Odd (r-(d+1)) then
        let a := greedy ((N+1)/(1-1/s))
        (a, f s (1-(N+1)/a))
      else
        let a := greedy (N/s)
        (a, g s (-N/a))

def rfiInitial (N : ℝ) (r : ℕ) : Fin r → ℕ :=
  fun i => (rfiState N r (r-1-i.val)).1

```

Lean block index i is source index i+1. `rfiState N r d` represents the source
state at index r−d; `rfiInitial` reverses those downward states into `Fin r`.
The special size at the last block is part of `Valid`, not an inferred
condition on the graph.

### The source algorithm and its initial choices

Source equations (5)–(6), p. 11, are

> f(X,Y) = (XY−1)/(X+Y−2),
> g(X,Y) = XY/(X+Y).

Algorithm 2, p. 16, has input “a positive real number N and a positive integer r”
and output “cotree T_G(a₁, a₂, …, a_r)”. Its choices and state updates, with
mathematical typesetting normalized, are:

> if r is odd then
> Choose a_r ≥ 1 + ⌊N+1⌋
> s_r ← 1 − (1+N)/a_r
> else if r is even then
> Choose a_r ≥ 2
> s_r ← −N/a_r
> end if
> for i = r−1 to 1 do
> if i is odd then
> Choose a_i ≥ 1 + ⌊(N+1)/(1−1/s_{i+1})⌋
> p_i ← s_{i+1} − (1−(N+1)/a_i)
> s_i ← f(s_{i+1}, 1−(N+1)/a_i)
> else if i is even then
> Choose a_i ≥ 1 + ⌊N/s_{i+1}⌋
> p_i ← s_{i+1} − N/a_i
> s_i ← g(s_{i+1}, −N/a_i)
> end if
> end for

Definition 13 concludes (mathematical typesetting normalized):

> then T_G(a₁, a₂, …, a_r) is called the initial threshold w.r.t. N, having no eigenvalues
> in the interval (0, N].

After Definition 13, the source states:

> Notice that the initial threshold is obtained by making the smallest choice for each a_i
> at RFI(N, r).

Definition 13 contains apparent state-subscript misprints in its displayed choices (also present in arXiv Definition 5.5). We use the unambiguous downward recursion in Algorithm 2, the explicit smallest-choice sentence, and the matching printed examples to identify the intended initial vector.

The Lean code immediately above implements these smallest choices. It does not
retain the p_i, since those are diagnostic diagonal outputs and do not affect
a_i or s_i. `greedy` uses the real floor to an integer, followed by `Int.toNat`.
`rfi_floor_nonneg` proves that every visited step has a nonnegative input to the
floor, and `greedy_cast` identifies the resulting real value with ⌊t⌋+1.
The base floor input N+1 is positive. `rfi_signs` proves the source's alternating
signs and `odd_step`/`even_step` also prove the f/g denominators are nonzero.
Thus the total definitions at irrelevant negative or out-of-range inputs are
never used to justify the conjecture.

Examples 14 and 15, p. 17, print `T_G(5,145,5,145,6)` for N=4.8, r=5 and
`T_G(6,44,6,36,5,2)` for N=4.8, r=6. Both are proved in Lean with real floors:

```lean
theorem example14 : rfiInitial (24/5) 5 = ![5,145,5,145,6]
theorem example15 : rfiInitial (24/5) 6 = ![6,44,6,36,5,2]
```

These use ordinary `norm_num` and kernel reduction. They cover both parities
with nontrivial recursive states. The source also prints the √5, depth-7
example `(4,10,4,55,3,12,4)`; this packet does not formally prove that example.

### Smaller and eigenvalue-free

Definition 23, p. 23 (extracted lines 1245–1252), reads:

> Let T_G(a₁, …, a_r) with a_i ≥ 1 for 1 ≤ i ≤ r−1 and a_r ≥ 2, and
> T′_G(b₁, b₂, …, b_r) be two threshold graphs. We say that G ≼ G′ if
> a_i ≤ b_i for i = 1, 2, …, r i.e., if G′ is generated from G by adding any
> amount of leaves to ∪-nodes or ⊗-nodes (of course, G ≺ G′ if G ≼ G′ and G ≠ G′).
> Notice that G and G′ have the same depth.

The corresponding hypothesis in the endpoint is exactly
`hle : ∀ i, b i ≤ rfiInitial N r i`.
The abstract states:

> A graph is said to be I-eigenvalue free if it has no eigenvalues in the interval I
> with respect to the adjacency matrix A.

The interval in the conjecture is (0,N], closed at N. The source defines an
eigenvalue by det(λI−A)=0 in §2. For a real finite matrix this is equivalent to
a nonzero real eigenvector. The Lean endpoint uses the latter directly; no
unproved graph-to-matrix convention is built into the word “free”.

```lean
def IntervalFree (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Prop :=
  ∀ μ : ℝ, 0 < μ → μ ≤ N →
    ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ,
      v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v

```

`Conjecture352345` is the unchanged stage-1 definition of the proposition.
The theorem `RFIMinimality.conj_10_1` proves the exact endpoint:

```lean
theorem conj_10_1 (N : ℝ) (hN : 0 < N) (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : Valid r b) (hle : ∀ i, b i ≤ rfiInitial N r i)
    (hfree : ∀ μ : ℝ, 0 < μ → μ ≤ N →
       ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ, v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v) :
    b = rfiInitial N r
```


## Proof as formalized

All block indices in this section are 1-based for readability; the displayed
Lean definitions use indices one less. Put O={i: i odd} and k=|O|. For a valid
block vector b, define the symmetric matrix B, based on block sums, by

\[
 B(N)_{ii}=\begin{cases}1-(N+1)/b_i&i\in O,\\-N/b_i&i\notin O,\end{cases}
 \qquad B(N)_{ij}=\mathbf1_{\min(i,j)\in O}\quad(i\ne j).
\]

Define C on O by

\[
 C(N)_{ij}=1+\frac1N\sum_{e\text{ even},\ e>\max(i,j)}b_e
       -\mathbf1_{i=j}\frac{N+1}{b_i}.
\]

Here and below q(A,x)=xᵀAx. These are proof auxiliaries, rather than changes
to the source graph or the meaning of eigenvalue freedom.

The auxiliary Lean definitions used for these forms are printed here; their
entry formulas follow directly from the source adjacency rule by the proved
block and parity bridges.

```lean
def oddBlocks (r : ℕ) := {i : Fin r // Odd (i.val+1)}
instance (r : ℕ) : Fintype (oddBlocks r) := by unfold oddBlocks; infer_instance
instance (r : ℕ) : DecidableEq (oddBlocks r) := by unfold oddBlocks; infer_instance

def B (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if i = j then
    if Odd (i.val+1) then 1-(N+1)/b i else -N/b i
  else if Odd ((min i j).val+1) then 1 else 0

def Cmat (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Matrix (oddBlocks r) (oddBlocks r) ℝ :=
  fun i j => 1 + (1/N) * (∑ e : Fin r,
    if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ) else 0)
    - (if i = j then (N+1)/b i.val else 0)

def qform {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  dotProduct x (A *ᵥ x)

def positiveOn {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (P : Submodule ℝ (n → ℝ)) : Prop :=
  ∀ x ∈ P, x ≠ 0 → 0 < qform A x

def nonpositiveOn {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (P : Submodule ℝ (n → ℝ)) : Prop := ∀ x ∈ P, qform A x ≤ 0

def blockLift {r : ℕ} (b : Fin r → ℕ) (y : Fin r → ℝ) :
    (Σ i : Fin r, Fin (b i)) → ℝ := fun x => y x.1 / b x.1

def decrement {r : ℕ} (a : Fin r → ℕ) (i : Fin r) : Fin r → ℕ :=
  Function.update a i (a i-1)

def suffixB (N : ℝ) (r j : ℕ) : Matrix {i : Fin r // j ≤ i.val} {i : Fin r // j ≤ i.val} ℝ :=
  (B N r (rfiInitial N r)).submatrix Subtype.val Subtype.val

```

### Literal graph and block forms

Let T send a vertex vector to its sum on each block, and let L send block
sums y to the vertex vector with value y_i/b_i in block i. Every b_i is
positive, so TL=I. Directly expanding the source adjacency rule gives

\[
 q(A-NI,Ly)=q(B(N),y),\qquad
 q(A-NI,v)\le q(B(N),Tv)\quad(N\ge0).                 \tag{1}
\]

For the inequality, apply (Σv)²≤b_iΣv² separately to each block, with
coefficient N+1 on an odd block and N on an even block. These are
`block_form` and `graph_form_le`; both refer to the actual adjacency matrix.

### Positive directions without an inertia theorem

For every valid b, B(0) has a positive subspace of dimension k. Prove this
by induction removing the first two blocks. If y denotes the coordinates
on the remaining suffix, add the first coordinates

\[
 (t,\ t-\textstyle\sum y,\ y).
\]

The exact form identity is

\[
 q(B(0),(t,t-\sum y,y))=(3-1/b_1)t^2+q(B_{\mathrm{suffix}}(0),y).  \tag{2}
\]

Since b₁≥1, the new coefficient is strictly positive. This map on the
product of ℝ and the suffix subspace is linear and injective: read t in
the first coordinate and y in the suffix. Its image therefore adds exactly
one positive dimension. The empty base has dimension zero. The one-block
base has coefficient 1−1/b_r>0, because b_r≥2. The odd-block cardinality
satisfies k(r+2)=1+k(r). This proves `B_positive_subspace`; applying L
proves `positive_subspace` for A.

### A C obstruction forces an adjacency eigenvalue

Reindex B(N) into odd and even blocks:

\[
 B(N)=\begin{pmatrix}A_O&X\\X^T&-D\end{pmatrix},\quad
 (A_O)_{ij}=1-\delta_{ij}(N+1)/b_i,\quad
 X_{ie}=\mathbf1_{i<e},\quad D_{ee}=N/b_e>0.
\]

Completion of the square gives C=A_O+XD⁻¹Xᵀ and

\[
 q(B(N),(x,z))\le q(C,x),                            \tag{3}
\]

with equality whenever Xᵀx=Dz. The entry identities, parity reindexing,
inequality, and stationary equality are all proved in Lean.

If x≠0 and q(C,x)≤0, pull back the line ℝx under restriction to odd
coordinates. Formula (3) makes B(N) nonpositive on this subspace Q, and
rank-nullity gives r<k+dim Q. Pull Q back through T; (1) makes the resulting
vertex subspace nonpositive for A−NI. Its dimension plus k exceeds the
number of vertices. The positive vertex subspace constructed above has
dimension k.

For completeness, the spectral dimension argument used in Lean is as
follows. Choose an orthonormal eigenbasis of A. Projection of any A-positive
subspace onto the coordinates λ>0 is injective, because a vector in its
kernel has nonpositive A-form. If there is no eigenvalue in (0,N], all those
positive eigenvalues exceed N. Projection of any (A−NI)-nonpositive
subspace onto the coordinates λ≤0 is then injective: a nonzero vector in
its kernel would have strictly positive (A−NI)-form. Their dimensions can
therefore sum to at most the ambient dimension, a contradiction. This
proves `eigenvalue_of_C_obstruction`, with a nonzero real adjacency
eigenvector and **0<μ≤N**. No inertia theorem or unproved spectral-count
identity is assumed.

### Constructive suffix responses

Let a be the literal greedy RFI vector. For every suffix j,…,r, we
construct w, extended by zero before j, such that

\[
 (B(a,N)w)_i=1\quad(i\ge j),\qquad \sum_iw_i=1/s_j.   \tag{4}
\]

This is `suffix_response_vector`. It replaces the inverse-matrix statement
of the ordinary proof by the precise constructive fact used below; no
claim of a formal determinant or inverse theorem is made.

For a final block, w has its sole entry equal to the reciprocal of the
nonzero last diagonal s_r. Suppose the deeper response has sum h=1/s.
At an even extension, whose diagonal is y=−N/a_j, adjoin 1/y and keep the
deeper vector. Its sum is 1/y+1/s=1/g(s,y). At an odd extension with
 y=1−(N+1)/a_j, put

\[
 w_j=\frac{1-h}{y-h},\qquad
 w_{>j}=\frac{y-1}{y-h}\,w_{\mathrm{old}}.
\]

The new row is y w_j+Σw_{>j}=1, and every deeper row is
w_j+(y−1)/(y−h)=1. The sum is

\[
 \frac{1-h}{y-h}+\frac{y-1}{y-h}h=1/f(s,y).
\]

The RFI signs are proved inductively from the strict floor inequalities;
s is negative at an even suffix and positive at an odd suffix. The odd
pivot y−1/s is nonzero: if it vanished, sy−1=0 and the next f-value would
be zero, contrary to its proved positive sign. Thus every construction is
defined. All real floor arguments are proved nonnegative, so Int.toNat
cannot introduce a truncated negative choice.

### Turning a response into a global C-vector

Consider any valid vector b and an odd index j. Suppose its deeper suffix
has a response w of sum h as in (4), and suppose B(b,N)_{jj}−h≤0. Set
v=e_j−w, with w zero through j. Then v_j=1, v is zero before j, and
(Bv)_i=0 for i>j. Also (Bv)_j=B_{jj}−h, so

\[
 q(B,v)=B_{jj}-h\le0.                               \tag{5}
\]

Every even row of Bv is zero: deeper rows already vanish, and earlier even
rows have no edges to the support of v. Hence Xᵀv_O=Dv_E, and the equality
case of (3) gives q(C,v_O)=q(B,v). The odd vector v_O is nonzero at j.
This is `odd_response_obstruction`. Because all vectors are extended by
zero in the original full index set, the obstruction is already global;
there is no paper-only principal-submatrix bridge.

### Every valid immediate decrement is obstructed

**Odd index j.** If j=r, the reduced diagonal is
1−(N+1)/⌊N+1⌋≤0 whenever the decrement is valid. Use the empty deeper
response, of sum zero, in (5). Otherwise the unchanged deeper response has
sum h=1/s_{j+1}<0. The greedy choice is
 a_j=⌊(N+1)/(1−h)⌋+1. After reduction,

\[
 1-\frac{N+1}{a_j-1}-h\le0.
\]

The denominator is positive by validity. This is the proved scalar
`odd_decrement_pivot`; (5) proves `odd_decrement`.

**Even index i.** The final even block is 2 and cannot be reduced validly.
Otherwise let s=s_{i+1}>0, b=a_i=⌊N/s⌋+1, u=b−N/s, and c=a_{i−1}.
Then 0<u≤1, s_i=−N/u, and

\[
 c=\left\lfloor\frac{N(N+1)}{N+u}\right\rfloor+1.
\]

We need the consecutive-floor bound

\[
 1-\frac{N+1}{c}+\frac{u-1}{N}\le0.                 \tag{6}
\]

Here is its full scalar proof. Put v=N+u−1. If v≤0, the expression is
v/N−(N+1)/c<0. If v>0, (N+u)v≤N(N+1), since N+u≤N+1 and v≤N.
Consequently N(N+1)/v−N(N+1)/(N+u)≥1. The floor bound
c≤N(N+1)/(N+u)+1 then gives c≤N(N+1)/v, equivalent to (6).
This argument is `paired_bound`/`paired_floor_bound`; `even_pair_pivot`
combines it with the literal successive greedy choices.

In the reduced vector the even block size is b−1>0. Extend the unchanged
deeper response by the entry −(b−1)/N at i. Its new sum is
h′=−(b−1)/N+1/s. At the preceding odd block i−1 the pivot is

\[
 1-\frac{N+1}{c}-h'
 =1-\frac{N+1}{c}+\frac{u-1}{N}\le0.
\]

Apply (5) there. This proves `even_decrement`, including equality in (6).

### Monotonicity and the endpoint

Direct expansion gives

\[
 q(C(b,N),x)=(\sum_{i\in O}x_i)^2
 -\sum_{i\in O}\frac{N+1}{b_i}x_i^2
 +\sum_{e\notin O}\frac{b_e}{N}(\sum_{i<e}x_i)^2.
\]

Thus b≤a implies C(b,N)≤C(a,N) as quadratic forms (`C_mono`). If valid
b≤a differs from a, choose i with b_i<a_i. The vector a−e_i is still
valid, since b_i provides its lower bound, and b≤a−e_i. The decrement
lemmas give a nonzero x with q(C(a−e_i,N),x)≤0. Monotonicity gives the
same inequality for C(b,N), and the spectral bridge supplies an adjacency
eigenvalue 0<μ≤N. This contradicts the freeness premise, proving b=a.

The final Lean theorem is `RFIMinimality.conj_10_1`; it has no residual
subspace, response, or decrement assumptions. Freeness of every initial RFI
graph is not needed for this implication and is not claimed as a formal
result here. The separate concrete graph TG(1,2)=P₃ at N=1 witnesses that
the endpoint's hypotheses can be satisfied.

## Significance and prior-art limits

The paired-even-block obstruction replaces exponential box searches by a
local certificate. This is a modest finite-linear-algebra result. The supplied
review flags a substantial risk that a specialist would regard the argument
as routine. Its mathematical contribution is the global obstruction from two
consecutive greedy choices, rather than the standard spectral machinery. Formalization alone
is not evidence of mathematical novelty.

The supplied review of 2026-11-20 found only arXiv v1 and the 2023 journal
version, where the problem remains Conjecture 29. Its checks of the three
Semantic Scholar citing titles, the 2026 threshold-graph survey, Omega
registry queries, Principia id/source searches and two web searches found
no public resolution. The survey cites the source's generating theorem,
not a minimality result. The review assigns provisional novelty confidence
and explicitly records the routine-risk caveat. This lane relies on that
bounded review; it has not refreshed public registries or performed a new
literature sweep. No universal novelty claim is made.

The review's counterweight paragraph is reproduced verbatim:

> To a specialist in Schur complements and inertia (the Jacobs–Trevisan–Tura school), the C-matrix reformulation is natural. Once it is in hand, the odd case is immediate and the even case is a one-paragraph floor computation. I put the probability that a referee calls this "an exercise" at about 45%.

## Formal artifacts

The exact compiled sources are in `src/`, in dependency order in
`LEAN-SOURCE-APPENDIX.md`. `REPORT.md` records the endpoint and auxiliary
statements, the axiom output, pinned runtime and successful compile and
standalone kernel-check receipts. The status is COMPLETE: the literal
`conj_10_1` has no residual theorem inputs. The original inverse/determinant
helper was replaced by constructive response vectors, as recorded in DESIGN.md.
