# Candidate: nonconvergence for every all-odd randomized subtraction set

Status: complete proposed mathematical proof; independent review and full Lean pending. One discovery candidate only. The root-simplicity conjecture MathDB363319 is not claimed proved.

## Exact source and scope

Nicolás Capitelli and Francisco Somma, *On sequences arising from randomizing subtraction games*, arXiv:2405.19593v1 (30 May 2024), Section3, Question3.4 and opening paragraph. Primary: <https://arxiv.org/html/2405.19593v1>. Local exact HTML: `sources/2405.19593v1.html`. The source states that nonconvergence for every finite all-odd subtraction set is not established for general cardinality; Question3.4 asks whether the coefficient of the root−1 is always nonzero. MathDB363319 extracts the neighboring root-simplicity Conjecture3.3 from this paper; this candidate bypasses that conjecture to resolve the stated motivating convergence question.

Let S be a nonempty finite subset of positive odd integers. At a heap of n chips select uniformly among eligible moves E_n={k∈S:k≤n}; a player with E_n empty loses. Let a_n be the probability the next player wins. Thus

\[
a_n=0\ (E_n=\varnothing),\qquad
a_n=1-\frac1{|E_n|}\sum_{k\in E_n}a_{n-k}\ (E_n\ne\varnothing).
\]

In particular a_0=0 and 0≤a_n≤1. No gcd assumption is needed for the nonconvergence conclusion below. Under the source's gcd(S)=1 assumption, the usual root localization identifies the two subsequential limits; their amplitude is quantified below.

## Zigzag inequalities

For all m≥0,
\[
a_{2m}\le a_{2m+1},\qquad a_{2m+2}\le a_{2m+1}.
\]

Prove the two inequalities successively by induction on m. First a_0≤a_1 from nonnegativity. Suppose the first inequality holds through m. The eligible sets at heaps2m+1 and2m+2 are identical, since all moves are odd. In each summand k=2h+1, the previous heap pair is (2m+1−k,2m+2−k)=(2(m−h),2(m−h)+1). The induction hypothesis makes the latter winning probability at least the former, so subtracting averages proves a_{2m+2}≤a_{2m+1}. Empty eligible sets give equality0.

Now compare heaps2m+2 and2m+3. If the old eligible set is empty, the old winning probability is0 and the new probability is nonnegative; this case is immediate without averaging. Otherwise, For each move already eligible at2m+2, the previous heaps are an odd number and its next even number, and the just-proved second inequalities make the new summand no larger. The eligible set at2m+3 either stays the same, or adds the single move k=2m+3, whose summand is a_0=0. Since all summands are nonnegative, adding this zero cannot increase their average. Subtracting averages proves a_{2m+2}≤a_{2m+3}. This completes the induction.

## A strictly positive invariant

Set c_n=(-1)^n(1−2a_n). Because every k is odd, the same recurrence becomes
\[
 |E_n|c_n=\sum_{k\in E_n}c_{n-k}\quad\hbox{for every }n\ge0,
\]
including empty eligible sets. Define the prefix sums C(h)=Σ_{j=0}^{h−1}c_j. For an odd h, pair each odd index with the following even index:
\[
 C(h)=1+2\sum_{j=1}^{(h-1)/2}(a_{2j-1}-a_{2j})\ge1.
\]

Let D=max S, t=|S|, and K=Σ_{k∈S}k. For n≥0 define
\[
 I_n=\sum_{k\in S}\sum_{j=0}^{k-1}c_{n+D-k+j}.
\]

All eligible moves are available at heap n+D, and telescoping gives
\[
 I_{n+1}-I_n=t c_{n+D}-\sum_{k\in S}c_{n+D-k}=0.
\]
So I_n=I_0. Sum the variable-eligibility recurrence over 0≤n<D and exchange its finite sums:
\[
 \sum_{k\in S}\sum_{n=k}^{D-1}c_n
 =\sum_{k\in S}\sum_{j=0}^{D-k-1}c_j.
\]
Equivalently,
\[
 \sum_{k\in S}C(k)+\sum_{k\in S}C(D-k)=tC(D).
\]
Consequently
\[
 I_0=\sum_{k\in S}(C(D)-C(D-k))=\sum_{k\in S}C(k)\ge t>0.
\]

This prefix/suffix identity is essential: replacing individual suffix sums by prefix sums is generally unjustified; equality holds for their total by the recurrence.

## Nonconvergence and amplitude

If a_n converged to L, the full-move recurrence at n≥D would imply L=1−L, so L=1/2. Then c_n→0, and the finite sum defining I_n would tend to0, contradicting I_n=I_0≥t. Thus **a_n does not converge for every finite nonempty all-odd subtraction set**, without any root-simplicity or gcd hypothesis.

If additionally gcd(S)=1, source Proposition3.1 gives that−1 is the unique unit-modulus characteristic root and is simple; all others have modulus<1. Repeated interior roots still decay after their polynomial factors, so the even and odd subsequences converge. If a_n=1/2+α(-1)^n+o(1), then c_n→−2α and the invariant gives
\[
 \boxed{\alpha=-\frac{\sum_{k\in S}C(k)}{2K}\le-\frac{t}{2K}<0.}
\]
In particular the even limit is strictly below1/2 and the odd limit strictly above1/2. This answers source Question3.4 in the all-odd setting in which that−1 coefficient is defined. For S containing an even move,−1 is not a root and the source already proves convergence; no new claim there.

## Sanity checks and novelty boundary

Exact rational checks for all4-element subsets of odd3..27 confirmed the prefix/suffix total identity and both zigzag inequalities through the checked range. These checks are not proofs.

The source's simplicity conjecture remains open. This candidate concerns the distinct motivating convergence question. Preliminary title/author searches have not found a later resolution; independent literature review is pending. Standard finite-sum telescoping and linear-recurrence asymptotics are tools, not claimed new discoveries.
