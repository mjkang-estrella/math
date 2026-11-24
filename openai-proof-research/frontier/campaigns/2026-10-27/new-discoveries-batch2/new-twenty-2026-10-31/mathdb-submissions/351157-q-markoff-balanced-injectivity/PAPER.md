# First jets distinguish finite balanced binary words

MathDB 351157 · Stage-1 formalization packet · 20 November 2026

**Certificate status: COMPLETE.** The exact conjecture endpoint and stronger finite-balanced theorem are proved. A fresh extraction from the printed appendix compiled and standalone-kernel-checked all 12 modules; sources and oleans match the author build exactly. The endpoint uses only propext, Classical.choice and Quot.sound. Independent final review and campaign acceptance remain separate.

## Statement and source conventions

Labbé and Lapointe, *The q-analog of the Markoff injectivity conjecture over the language of a balanced sequence*, arXiv:2106.15886v3, Conjecture 1.3, states:

> The map {0,1}* → ℤ[q] defined by w ↦ μ_q(w)₁₂ is injective over the language L(B) = ⋃_{s∈B} L(s) of all balanced sequences.

Their §2.1 defines the language:

> Let s ∈ Σ^ℤ be a sequence over a finite set Σ. The language of s is L(s) = {s_k s_{k+1} ··· s_{k+n−1} | k ∈ ℤ, n ≥ 0} ⊂ Σ* is the set of subwords (or factors) occurring in s.

Their Definition 2.1 is:

> A sequence s ∈ Σ^ℤ is balanced if for every positive integer n, for every u,v ∈ L(s) ∩ Σ^n and every letter a ∈ Σ, the number of a’s occurring in u and v differ by at most 1.

In §1.1 their matrices and morphism are

\[
\mu_q(0)=\begin{pmatrix}q+q^2&1\\q&1\end{pmatrix},\qquad
\mu_q(1)=\begin{pmatrix}q+2q^2+q^3+q^4&1+q\\q+q^2&1\end{pmatrix}.
\]

> Therefore, this defines a morphism of monoids μ_q : {0,1}* → GL₂(ℤ[q^{±1}]).

The entries of all finite products are integer polynomials. The Lean definitions immediately corresponding to these source definitions are:

```lean
def mu0 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) := !![X + X^2, 1; X, 1]
def mu1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![X + 2*X^2 + X^3 + X^4, 1 + X; X + X^2, 1]
def muq (w : List Bool) : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  (w.map fun b => if b then mu1 else mu0).prod

def onesIn (s : ℤ → Bool) (i : ℤ) (l : ℕ) : ℕ :=
  ((List.range l).filter fun t => s (i + t)).length

def BalancedSeq (s : ℤ → Bool) : Prop :=
  ∀ (i j : ℤ) (l : ℕ), (onesIn s i l : ℤ) - onesIn s j l ≤ 1

def IsFactor (w : List Bool) (s : ℤ → Bool) : Prop :=
  ∃ i : ℤ, w = List.ofFn fun t : Fin w.length => s (i + t)

def LB : Set (List Bool) := {w | ∃ s, BalancedSeq s ∧ IsFactor w s}
```

Here false encodes 0 and true encodes 1. `List.prod` multiplies left to right and sends the empty word to the identity. Both orders of i,j occur in `BalancedSeq`, so it bounds the absolute difference in ones. Equal-length binary factors have zero-count difference equal to the negative of their one-count difference. Thus the all-letter source condition is exactly the displayed binary condition; length zero adds only 0 ≤ 1. `IsFactor` is literal consecutive occurrence, with no periodicity or slope restriction.

We prove the stronger assertion of injectivity on finite balanced words. In Lean, `FiniteBalanced w` compares the one-counts of every pair of windows of equal length contained in w. `factor_window_count` and `LB_finiteBalanced` prove the bridge from the source language inside Lean.

## Strict mechanical prefixes without Sturmian theory

For a window of length l at i write c(i,l) for its number of ones. If w is finite balanced and l,m are positive contained window lengths, then

\[
c(i,l)m-c(j,m)l<l+m. \tag{1}
\]

Induct on l+m. For l=m, balance gives the left side at most l, less than 2l. For l<m, split the second window into a prefix of length l, with count d₁, and a suffix of length m−l, with count d₂. Balance gives c−d₁≤1, and induction gives c(m−l)−d₂l<m. Therefore

\[
cm-(d_1+d_2)l=[c(m-l)-d_2l]+(c-d_1)l<m+l.
\]

For l>m, split the first window into lengths m and l−m and apply the same argument. All pieces remain windows of the original word, so no extension theorem is used. This is `balanced_cross_window`.

Consider the finite open intervals

\[
I_{i,l}=((c(i,l)-1)/l,(c(i,l)+1)/l).
\]

Equation (1) says that every lower endpoint is strictly less than every upper endpoint. The largest lower endpoint and smallest upper endpoint therefore bound a nonempty open interval. Choose α in it. For every positive contained window,

\[
c(i,l)-1<l\alpha<c(i,l)+1. \tag{2}
\]

Let n=|w| and P_t be the one-count in the first t letters. The finite intervals

\[
(P_t-t\alpha,P_t+1-t\alpha),\qquad 0\le t\le n,
\]

also have every lower endpoint below every upper endpoint. For i<j this follows from the upper inequality in (2) applied to the window [i,j); for i>j it follows from the lower inequality. Choose ρ in their common interval. Hence

\[
P_t<t\alpha+\rho<P_t+1\quad(0\le t\le n). \tag{3}
\]

In particular 0<ρ<1 and nα+ρ>k, where k=P_n. No bound on α is required. The empty-word case is covered by the same finite-separation argument. `finiteBalanced_strictFloor` proves (3) from the combinatorial predicate, with no additional assumptions.

## Recovering counts from the sixth-root value

Put ζ=(1+i√3)/2. Exact arithmetic gives ζ²=ζ−1, ζ³=−1, ζ⁶=1, and Im ζ≠0. Put

\[
N=\begin{pmatrix}\zeta&1-\zeta\\1&-\zeta\end{pmatrix}.
\]

Then N²=0, M₀(ζ)=ζ(I+N), and M₁(ζ)=ζ²(I+(2−ζ)N). Induction on the word yields, with W=n+k,

\[
\mu_\zeta(w)=\zeta^W(I+[n+(1-\zeta)k]N),\qquad
p_w(\zeta)=\zeta^W(n-W\zeta). \tag{4}
\]

This is the published zeroth-order evaluation of Labbé–Lapointe–Steiner, re-derived in `root_value_matrix` and `root_value`.

For completeness, count recovery needs no degree information. The integer coordinates of ζ^r(n−(n+k)ζ), for r=0,…,5, are respectively

\[
(n,-n-k),\ (n+k,-k),\ (k,n),\ (-n,n+k),\ (-n-k,k),\ (-k,-n).
\]

Under 0≤k≤n, equality of coordinate pairs from any two rows implies equality of n and k, including n=0. This follows by the thirty-six elementary pairs of linear inequalities; `phaseCoords_injective` checks these using integer arithmetic. Since 1 and ζ are linearly independent over ℝ in their real coefficients, equal root values determine n,k. The Lean theorem `polynomial_recovers_counts` applies this directly to equal integer polynomials. This step is not claimed as new.

## First derivatives recover two prefix moments

Use prefix versions of the two position statistics, defined directly by

\[
A_*(w)=\sum_{t=0}^n[k+(k-1)P_t-P_t^2],\qquad
B_*(w)=-\sum_{t=0}^n(2t-n)P_t. \tag{5}
\]

These are `wordMomentA` and `wordMomentB`. Our proof uses (5) throughout; it requires no unformalized equivalence to position statistics. Relative to the proof candidate's sums over t=1,…,n−1, these add k to A and subtract nk from B, which depend only on counts.

The source matrices satisfy the exact polynomial identity

\[
M_1M_0-M_0M_1=(q+q^4)\begin{pmatrix}0&1\\-q&0\end{pmatrix}.
\]

Let K=3[[0,1],[−ζ,0]]. The commutator vanishes at ζ and its derivative there equals −K. Moreover KN=−NK and NKN=0. Therefore, for arbitrary prefix x and suffix y, differentiating the difference x10y−x01y leaves only

\[
\mu_\zeta(x)(-K)\mu_\zeta(y).
\]

The other terms vanish because they contain the undifferentiated commutator. If i=|x|, r=|x|₁ and n,k are the total counts, (4) and

\[
[(I+aN)K(I+bN)]_{12}=3[1+\zeta(a-b)]
\]

give the exact scalar difference

\[
p'_{x10y}(\zeta)-p'_{x01y}(\zeta)
=3\zeta^{n+k}\{(2r+2-k)+\zeta(2i+2-n)\}. \tag{6}
\]

Only the prefix at t=i+1 changes in the swap: its count decreases from r+1 to r. Thus (5) gives

\[
A_*(x10y)-A_*(x01y)=k-2r-2,\quad
B_*(x10y)-B_*(x01y)=n-2i-2. \tag{7}
\]

Equations (6)–(7) show that

\[
J(w)=p'_w(\zeta)+3\zeta^{n+k}[A_*(w)+\zeta B_*(w)] \tag{8}
\]

is unchanged under an adjacent interchange. Equal-count binary words are permutations of each other, and adjacent interchanges generate permutations. The Lean proof explicitly carries arbitrary prefix contexts through the permutation induction. Consequently equal-count words have equal J. If p_u=p_v, count recovery and equality of derivatives in (8) imply equal A_* and B_*, because 3ζ^{n+k}≠0 and ζ is nonreal.

## The energy reconstruction

For an integer prefix vector P satisfying (3), define

\[
E_{\alpha,\rho}(Q)=\sum_{t=0}^n[Q_t^2-(2t\alpha+2\rho-1)Q_t].
\]

If p<x<p+1 and q≠p are integers, then

\[
q^2-(2x-1)q-[p^2-(2x-1)p]=(q-p)(q+p-2x+1)>0.
\]

For q>p both factors are positive; for q<p both are negative. Hence P uniquely minimizes E among integer vectors, coordinate by coordinate.

Suppose P,Q have the same endpoints P₀=Q₀=0, P_n=Q_n=k and the same moments (5). Write S=Σ(P_t−Q_t). Expanding the definitions gives the exact identity

\[
E_{\alpha,\rho}(P)-E_{\alpha,\rho}(Q)
=-(n\alpha+2\rho-k)S. \tag{9}
\]

More generally, the right side has the additional terms −(A_*(P)−A_*(Q))+α(B_*(P)−B_*(Q)); `energy_difference` proves this identity without balance assumptions. From (3) at t=0,n, the coefficient nα+2ρ−k is positive. If P≠Q, strict minimality and (9) imply S>0. Using the mechanical parameters of Q instead gives −S>0, a contradiction. Thus P=Q. Successive prefix differences recover each Boolean letter, so the words are equal. `finiteBalanced_moments_injective` formalizes this reconstruction.

Combining count recovery, moment recovery, reconstruction, and `LB_finiteBalanced` proves the literal Conjecture 1.3 endpoint. There are no common-sequence, fixed-slope, nonempty-word, or bounded-length hypotheses.

## Fidelity and nonvacuity

The certificate includes the two distinct equal-count words 0010100 and 0100010 in LB. They occur at offset zero in the periodic sequences (00101)^∞ and (0100)^∞, respectively. Balance is proved for arbitrary integer starts and arbitrary window lengths by reducing the length modulo the period. No balanced sequence contains both: 0010100 contains 101 with two ones, whereas 0100010 contains 000 with no ones.

The source example is checked exactly:

\[
p_{00101}=1+4q+10q^2+18q^3+27q^4+33q^5+33q^6+29q^7+21q^8+12q^9+5q^{10}+q^{11}.
\]

It fixes product order and the selected matrix entry. The known collision p_{00011}=p_{01001} is also checked, and 00011∉LB is proved: its length-two factors 00 and 11 violate balance. These checks establish that the balance condition has substantive content.

## Prior art, significance and limits

The supplied independent review states:

> What the authors had: Theorem A (monotonicity in radix order inside one balanced language), and, in the follow-up, the ζ₆ evaluation that recovers (n,k). Neither compares factors of different balanced sequences with the same counts, which is the whole difficulty: for example 0010100 (a factor of (00101)^∞) and 0100010 (a factor of (0100)^∞) have equal counts and lie in no common balanced sequence. The authors had the ζ₆ tool in 2022–24 and left Conjecture 1.3 open.

Labbé–Lapointe–Steiner, *A q-analog of the Markoff injectivity conjecture holds*, Algebraic Combinatorics 6(6) (2023), 1677–1685, DOI 10.5802/alco.322, arXiv:2212.09852v4, proves injectivity on Christoffel words and supplies the root-value count recovery. The contribution under review is first-order recovery of two prefix moments and strict quadratic reconstruction across distinct balanced languages. The elementary interval proof here also removes the proof candidate's dependence on the finite Sturmian-factor characterization.

This does not prove classical Markoff injectivity at q=1 or injectivity on all binary words. The novelty assessment rests on the supplied Opus review, including its explicitly limited citation coverage; no fresh worldwide-priority claim is made. Campaign acceptance and independent final review remain root responsibilities. Nothing has been submitted or published.

## Certificate map

The source appendix contains every retained module in import order. `MarkoffStatement` implements the literal definitions; `MarkoffChecks` and `MarkoffFactors` prove fidelity and inheritance; `BalancedFloor` proves (1)–(3); `MarkoffRoot` and `MarkoffCounts` prove (4) and recover counts; `MarkoffEnergy` proves reconstruction; `MarkoffJetLocal`, `MarkoffSwapMoments`, and `MarkoffJetSwap` prove (6)–(8); `MarkoffConjecture` assembles the endpoint. See REPORT.md for final kernel and replay status and printed axioms.

## References

1. S. Labbé and M. Lapointe, *The q-analog of the Markoff injectivity conjecture over the language of a balanced sequence*, Combinatorial Theory 2(1) (2022), #9; [arXiv:2106.15886v3](https://arxiv.org/abs/2106.15886v3), DOI [10.5070/C62156881](https://doi.org/10.5070/C62156881). Conjecture 1.3, Definition 2.1 and §1.1.
2. S. Labbé, M. Lapointe and W. Steiner, *A q-analog of the Markoff injectivity conjecture holds*, Algebraic Combinatorics 6(6) (2023), 1677–1685; [arXiv:2212.09852v4](https://arxiv.org/abs/2212.09852v4), DOI [10.5802/alco.322](https://doi.org/10.5802/alco.322). Lemma 2.1, Proposition 2.3 and Theorem 1.2.

Primary-source text and the prior-art findings were supplied by the proof and independent pre-Lean review lanes. The input hashes are recorded in `pin-verification.json`.
