# Monochromatic-box matrix — MathDB 317856

**Result:** a complete formalized verification of a known theorem. The original matrix is defined in Cooper–Fenner–Purewal, [arXiv:0810.3019v1](https://arxiv.org/html/0810.3019v1), Definition 7.2; its positivity is Conjecture 7.4. The published version renumbers these as Definition 16 and Conjecture 18.

**Prior resolution:** Cooper–Forst, [arXiv:1704.01644v2](https://arxiv.org/html/1704.01644v2), Corollary 3, proves positivity for all r ≥ 0. Proposition 4 gives the general set-intersection Gram argument. This packet does not claim to newly resolve that problem or discover that proof.

## Exact statement

Rows and columns are binary colorings f,g of an r-element ground set. Write A_c(f,g) for positions where both colorings use color c. Then

\[
M_r(f,g)=\binom{|A_0(f,g)|}{2}+\binom{|A_1(f,g)|}{2}.
\]

For every nonnegative integer r, this real symmetric matrix is positive semidefinite. Colors 0 and 1 are a relabeling of the source's 1 and 2; the row set is the function type `Fin r → Fin 2`, rather than an arbitrary enumeration by integers. No spectral formula is needed or claimed.

## Proof and formal generalization

For a finite ground set A, a finite color set C, and k ≥ 0, define

\[
M(f,g)=\sum_{c\in C}\binom{|\{a:f(a)=g(a)=c\}|}{k}.
\]

Index features by pairs (c,T), where T is a k-element subset of A. Define B(f,(c,T)) to be 1 when f is constantly c on T, and 0 otherwise. The inner product of rows f and g counts precisely the k-element subsets of their common color fibers. Hence M=BBᵀ, and for every real vector v,

\[
v^TMv=\sum_{c,T}\left(\sum_{f:\,f|_T=c}v_f\right)^2\ge0.
\]

In Lean, features range over *all* finite subsets; features of the wrong cardinality have zero incidence. `feature_count` proves that their sum is exactly the binomial coefficient using `Finset.card_powersetCard`. Thus no counting identity is left as an assumption.

## Formal coverage

- `commonFiber`, `boxMatrix`, `incidence`: complete finite definitions.
- `feature_count`, `gram_identity`: exact combinatorial Gram factorization.
- `boxMatrix_posSemidef`: arbitrary finite colors, arbitrary k.
- `sourceMatrix`, `sourceMatrix_eq_boxMatrix`: literal two-summand source formula and its equality to the general construction.
- `mathdb317856`: source-matrix positivity for every r.

The final positivity step uses `Matrix.posSemidef_self_mul_conjTranspose` and the standard real star-ordered-ring instance. All combinatorial reduction steps are in this packet.

## Status

The retrieved MathDB record says open and lists no posted solutions. That database status is outdated: the 2017 paper explicitly resolves the question and presents the underlying Gram argument. Count this as one distinct, fully checked mathematical outcome only if the campaign permits known-result formal verification; do not count it as a previously open problem solved here.

The packet contains both original and resolving source snapshots, a hash manifest, complete Lean code, compiler/axiom reports, and `paper/main.tex`. No PDF was requested or built.
