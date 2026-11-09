# Candidate: negative-order Vendi–LCR dominance without full rank

Status: proposed complete mathematical proof of the remaining singular negative-order case; independent source/novelty review and full matrix Lean bridge pending. No count assigned. The positive-order comparison is already proved in the latest primary source and is not new.

## Exact source and remaining scope

Phuc Nguyen, Josiah Couch, Rahul Bansal, Alexandra Morgan, Chris Tam, Miao Li, Rima Arnaout, and Ramy Arnaout, *Which Similarity-Sensitive Entropy (Sentropy)?*, arXiv:2511.03849v4 (30 March2026): <https://arxiv.org/html/2511.03849v4>. Current arXiv abstract and complete history were checked; v4 is latest. Local exact HTML is `sources/2511.03849v4.html`. A public primary PMC copy is <https://pmc.ncbi.nlm.nih.gov/articles/PMC12642762/>.

Original v1 Conjectures1–2 / MathDB371345–371346 compare Vendi score and Leinster–Cobbold–Reeve diversity for every real order. **Latest v4 Theorem1 already proves every q≥0, and q<0 when Z is full rank.** Its abstract, theorem statement, SectionIII Case5, and discussion retain that full-rank restriction. Those old cases are excluded from this candidate.

Let Z be a real symmetric positive semidefinite n×n matrix, n>0, with Zii=1 and0≤Zij≤1. Write Ri=Σj Zij≥1 and λ1,...,λn≥0 for eigenvalues. The Vendi convention discards zero eigenvalues: the source's archived implementation explicitly selects eigenvalues e>0 before computing powers. Thus for finite q≠1,

\[
 \operatorname{VS}_q(Z)=\left(\sum_{\lambda_j>0}(\lambda_j/n)^q\right)^{1/(1-q)},\qquad
 D_q(Z,1/n)=\left(\frac1n\sum_i(R_i/n)^{q-1}\right)^{1/(1-q)}.
\]

For q<0, the comparison is equivalent to

\[
 \sum_{\lambda_j>0}\lambda_j^q\ge\sum_iR_i^{q-1}.
\]

Zero eigenvalues are omitted, not assigned an infinite negative power. This support convention is essential. Epsilon-regularization of a singular Z would diverge for negative q and would not prove the asserted finite support inequality.

## Proposed stronger inequality, valid for every finite real q<1

Define Ei=Σj Zij²=(Z²)ii. Then

\[
 \boxed{\sum_{\lambda_j>0}\lambda_j^q
 \;\ge\;\sum_iE_i^{q-1}
 \;\ge\;\sum_iR_i^{q-1}.}
\]

The positive-order overlap with the existing source is background; the new application under review is q<0 with arbitrary rank.

Choose an orthonormal eigenbasis u1,...,un. For each row i define weights on the positive spectrum by

\[
 w_{ij}=\lambda_j|u_j(i)|^2\quad(\lambda_j>0).
\]

They are nonnegative and sum to Zii=1. Their weighted mean of the eigenvalues is

\[
 \sum_{\lambda_j>0}w_{ij}\lambda_j
 =\sum_j\lambda_j^2|u_j(i)|^2=(Z^2)_{ii}=E_i\ge1.
\]

The function x↦x^(q−1) is convex on(0,∞) for q<1. Scalar weighted Jensen, applied separately at each row, gives

\[
 E_i^{q-1}
 \le\sum_{\lambda_j>0}w_{ij}\lambda_j^{q-1}
 =\sum_{\lambda_j>0}\lambda_j^q|u_j(i)|^2.
\]

Sum over i and use Σi|u_j(i)|²=1 to get the first inequality. Since each0≤Zij≤1, Ei=Σj Zij²≤Σj Zij=Ri. The exponent q−1 is negative, so Ei^(q−1)≥Ri^(q−1), proving the second inequality.

Multiplication by n^(−q)>0 and taking the positive power1/(1−q) prove VSq≥Dq for every finite q<0 with no full-rank assumption.

## Order minus infinity

Let λmin be the smallest positive eigenvalue. Each Ei is a convex combination of positive eigenvalues under the weights above, so λmin≤Ei≤Ri for every i. Consequently

\[
 \operatorname{VS}_{-\infty}(Z)=n/\lambda_{\min}
 \ge n/\min_iR_i=D_{-\infty}(Z,1/n).
\]

Together with latest-source Theorem1 this mathematically supplies the entire original order range. Any Lean claim must state exactly which part is formalized; the known positive-order theorem is not silently treated as a new axiom.

## Weighted-distribution extension, the same candidate

The same proof extends beyond uniform p. For strictly positive probabilities pi summing to1, put A=diag(sqrt(p)) Z diag(sqrt(p)), whose eigenvalues sum to1, and ri=(Zp)i. The row weights λj|uj(i)|²/pi sum to1. Their mean is (A²)ii/pi=Σj pj Zij²≤ri. Multiplying each row's Jensen inequality by pi yields

\[
 \sum_{\lambda_j>0}\lambda_j^q
 \ge\sum_i p_i\left(\sum_jp_jZ_{ij}^2\right)^{q-1}
 \ge\sum_i p_i(Zp)_i^{q-1}\quad(q<1).
\]

This is one strengthening of the same support comparison, not an additional discovery count.

## Prior-art boundary

Scalar Jensen, spectral decomposition, and matrix power inequalities are classical and are not claimed new. The latest source has an explicit unresolved singular negative-order gap, but that alone does not demonstrate novelty. Independent review must determine whether an older general trace/diagonal-moment inequality already states this exact stronger bound, and must search current Vendi/LCR literature for a prior comparison. No costly matrix formalization or discovery credit should precede that check.
