# Fresh full target investigated; no full resolution

Credit **0**. This lane makes no eligibility, priority, novelty, formal-verification or acceptance claim. Campaign totals remain five additional / thirty-five total. Root alone owns the gates. No PROOF.md, Lean, paper or nomination is warranted.

## Selection and early screen

Ancestor and batch AGENTS.md, ledger, prior-campaign context and relevant Sol r5–43 summaries were consulted. `context-screen.json` inventories the context files with hashes and opening scope/status paragraphs; the user-supplied exclusions control selection. Earlier rounds r1–4 are represented by the campaign ledgers and earlier Astra/Pi work, not invented Sol summary filenames. No offlimits family was pursued.

Three primary question statements were screened before the determinant computation:

1. Ma–Weigert, *Complete monotonicity of log-functions*, Analysis and Mathematical Physics 15:141 (published 6 November 2025), Question 1.2: membership of CM_s intersect F_s, where F consists of p(log x)/(product x_i). The actual Theorems 1.3–1.4 in the SAME primary body give the full linear-isomorphism answer through nonnegative polynomials. The bridge is inverse Laplace transformation: monomials in log(t) integrate to a triangular linear transformation with Gamma derivatives at 1. This is already public; no new question or credit is inferred from that question heading. Publisher full HTML was obtained (despite a cookie-error parameter in the final URL).
2. Lamkin–Tkocz, arXiv:2001.06439v3, Conjecture 1: every iid nonnegative law and every real p>1 gives log-convex E[(S_n/n)^p]. Actual original statement/Remark 6 and Gonçalves–Madrid–Ramos arXiv:2608.00813v1 Theorem 1/Corollary 2 and application were read. Their convex-order theorem for products of disjoint normalized blocks applies to partitions (n,n) majorized by (n+1,n-1) of 2n. Testing with t^p and using independence gives exactly b_n^2 <= b_(n-1)b_(n+1), for all n>=2. Already public on 1 August 2026. Classical convex order of linear averages alone does NOT suffice: (uv)^p has Hessian determinant p^2(1-2p)u^(2p-2)v^(2p-2)<0. The new public product theorem supplies precisely the missing bridge. No new result claimed.
3. Selected: Koutschan–Krattenthaler–Schlosser, arXiv:2401.08481v1, **Conjecture 17**, p24 (author-hosted expanded PDF also p24), tied to Theorem 16, equation (8.10). This is a full all-order polynomial identity, away from the screened graph-index families. The arXiv history currently lists only v1, submitted 16 January 2024. Journal: J. Symbolic Computation 127 (2025), 102352. Publisher HTTP403 was respected; indexed publisher body corroborates that the polynomial-factor question is left open, but direct complete VoR comparison remains unavailable.

No fourth question was selected. E-determinant formulas, G-determinant identities, and Di Francesco's original determinant were not additional targets.

## Exact selected source statement

Use generalized binomial binom(a,k)=a(a-1)...(a-k+1)/k! for k>=0. For n>=1 let

D_n(x)=det_(0<=i,j<n)[4^i binom(x+i+2j+3,2j+3)+binom(x-i+2j+3,2j+3)].

The proved source Theorem 16 states D_n(x)=C_n(x) P_n(x), with monic P_n of degree 2n-2 and

C_n(x)=2*6^(n(n-1)/2) * product_(i=0)^(n-1) i!/(2i+3)! * (x+2)(x+3) * product_(i=0)^(n-1)(x+3i+1)_(n-i),

where (a)_k is rising factorial. Conjecture 17 requires, for EVERY integer n>=1, as an identity in Q[x],

3 P_(n+3) - 2 A_n P_(n+2) + B_n P_(n+1) - C'_n P_n = 0,

A_n=18n²+9nx+72n-3x²-3x+49,

B_n=135n⁴+108n³x+810n³-54n²x²+108n²x+1395n²-52nx³-510nx²-1100nx+120n-9x⁴-152x³-855x²-1780x-1020,

C'_n=6(n+1)(n-x-2)(n+x+2)(3n+x+3)(3n+x+5)(3n+x+7),

P_1=1, P_2=x²+31x/3+20, P_3=x⁴+26x³+229x²+6956x/9+2560/3.

A proof only for fixed x, bounded n, or a different normalization would not resolve this target.

## Nearest actual theorem bodies and public screen

Source Theorem 15/equation (8.9) evaluates the same matrix with lower indices 2j+1 instead of 2j+3; its proof invokes the holonomic Ansatz. Source Theorem 16's eight-step proof identifies factors, bounds the residual degree, and computes the leading coefficient. Those steps do NOT determine all coefficients of the residual monic degree-2n-2 polynomial. Both theorem bodies and the source discussion of their limitation were read.

Chen–Chern–Yoshida arXiv:2507.15665v2 (17 September 2025), actual Theorems 1.1, 1.2, 1.4 and their determinant definitions: tiling interpretations for two parameter subclasses and product evaluations (10.8),(10.9). In their notation the selected F determinant is B^(2,4)_(3,0,x+3,x+3). The first interpreted subclass requires the top shift to equal lower shift a; the selected x parameter breaks this except at x=0. The second subclass also has exponent offset 1 and incompatible shifts. Neither theorem yields the selected arbitrary-x factor recurrence. A tiling interpretation alone would in any event not prove that recurrence.

Current Omega bodies for KKS shifted-G, ten-ten and ten-eleven were read completely from archived files. They prove Conjecture 23 equations (10.10)–(10.12), using the G family's 2^i/4j entries and a fixed rational column multiplier. Our target uses 4^i/2j and a free x. Their bodies expressly retain other conjectures' independent evidence. No substitution or theorem-body bridge from those G results to Conjecture 17 was established. Their existence is not treated as clearance for F.

Current bounded searches included exact paper title plus recurrence, polynomial factor plus Koutschan, and exact Conjecture 17. Returned Kauers–Koutschan permutation recurrences are a DIFFERENT 2023 source, not this three-author 2024 determinant. No same-object settlement was located in this bounded search. This is not novelty evidence or an exhaustive citing-literature claim.

## Concrete all-order route and where it stops

Let A_N(x) be the Theorem 15 matrix with entries a_(i,j)=4^i binom(x+i+2j+1,2j+1)+binom(x-i+2j+1,2j+1). Then D_n(x) is EXACTLY its (n+1)-size minor deleting last row and first column. Over Q(x),

D_n(x)=(-1)^n det(A_(n+1)(x)) [A_(n+1)(x)^(-1)]_(0,n).

Thus a uniform boundary-inverse formula, or a uniform recurrence for that inverse entry with the known source determinant product, would resolve the question. Jacobi/Desnanot condensation introduces other mixed row/column deletions; the known full determinant values alone do not fix these entries. No closed system of those minors was obtained.

There is an exact row-basis simplification. Put H(t)=(1-t)^(-x-1), lambda=4/(1-t), mu=1-t, w=lambda+mu, v=w-5=t(3+t)/(1-t). Row i of A (or D) is odd-coefficient extraction from H(t)(lambda^i+mu^i). Since lambda*mu=4, S_0=2,S_1=w and S_i=w*S_(i-1)-4*S_(i-2); S_i is monic in w for i>=1. A triangular row change therefore proves, for either s=1 or s=3,

det[4^i binom(x+i+2j+s,2j+s)+binom(x-i+2j+s,2j+s)]
=2 det[[t^(2j+s)] H(t) v(t)^i].

This is a formal-series identity in Q[x], not an asymptotic or a numerical assertion. Its entries equal sum_(l=0)^i binom(i,l)3^(i-l) binom(x+2j+s-l,2j+s-i-l). The missing step is a uniform recurrence for the shifted odd-coefficient minors of this Riordan-type array. Stating the row transformation is not that proof.

## Strongest exact route falsifier

A routine ordinary-orthogonal-polynomial reduction fails already at the source's printed initial polynomials. Division gives

P_3=(x²+47x/3+424/9)P_2 -736x/27-800/9.

Hence no recurrence P_3=Q_2(x)P_2-c P_1 with monic quadratic Q_2 and x-independent c exists. Also no fixed monic quadratic coordinate y=x²+a x+b makes P_n a monic polynomial of degree n-1 in y: P_2 forces a=31/3, while P_3 would then have x³ coefficient 62/3 instead of 26. This rules out these simple Favard/quadratic-coordinate bridges; it does NOT refute Conjecture 17 or all possible multiple-orthogonality approaches.

## Checks, limits and unresolved gate

`bash run.sh python3 check.py` passes 112 exact source-recurrence evaluations (n=1..8, each at 2n+5 nonnegative integer x), 56 row-transform determinant checks and 28 literal minor checks, plus initial values and the symbolic division falsifier. Since source Theorem 16 bounds the residual degree by 2n+4, those x grids corroborate the recurrence polynomial identities at each of these EIGHT orders. They say nothing about arbitrary n. No floating numerical diagnostics were used. These are not nominated partial discoveries.

AS512MiB, CPU210s, alarm225s, timeout process-group wall230s/kill-after2s and BLAS1 are enforced; final exact run took under one second. First checker run had a hand-entered expected division remainder wrong; the assertion stopped, then the exact symbolic remainder was corrected. All preceding determinant tests had passed; no mathematical source claim depended on the wrong expected number.

Strongest objection to promotion: there is no all-order cofactor recurrence proof and no genuine source counterexample. Eligibility and broader literature coverage are also unpassed. No formal or manuscript investment follows from these finite checks. Honest zero-credit handback.
