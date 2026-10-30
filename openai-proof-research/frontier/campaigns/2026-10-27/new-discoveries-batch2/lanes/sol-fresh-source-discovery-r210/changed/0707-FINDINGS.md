# Mixed commutator and alternating-polynomial investigation — 2026-10-28

No new outcome is nominated. These are bounded computational evidence,
source exclusions and an elementary supporting observation, all credit zero.

## 1. Mixed inner product, actual source target

The precise conjecture following Theorem 1 of Chruscinski–Kimura–Ohno–Singal,
arXiv:2208.10005v1, LAA 656 (2023)158–166, was read in actual source HTML.
The publisher's indexed primary page also reproduces the complete Theorem 1
and conjecture: all real q, all complex square matrices, sharp constant

    c(q)=(1+q+sqrt(2(1+q^2)))/2

for Re<[B,A],[B,A]_q>. This is not the squared deformed-commutator norm.
The theorem is already known for n=2 or one normal factor. The publisher's
direct HTTP response to this environment was 403; retrievals.json records
that limit. The actual publisher excerpt was read via the web tool at
https://www.sciencedirect.com/science/article/abs/pii/S0024379522003470.
No full journal PDF or acceptance-grade novelty clearance is claimed here.

search.py constructs both Hermitian operators for optimization in one
matrix while fixing the other; it verifies each vectorization formula
against literal matrix multiplication, including negative q. An alternating
largest-eigenvector search covered n=2,3,4,5,6 and thirteen q-values from
-100 to 100, twelve starts per cell and at most 65 iterations. All 65 cells
attain c(q) to floating precision; maximum signed excess is 1.99e-13.
54 separate operator-identity checks passed. This is numerical evidence,
not a proof. No possible-witness file was produced. Additional similar
search is not justified without a new mechanism.

## 2. A nearby conjecture is already publicly solved

Nobori's arXiv:2506.17365v2 / LAA725(2025)135–144 Conjecture3.1 is the
spectral-middle-factor inequality with coefficient TWO and the top two
singular values of an OUTER matrix. It is MathDB368941 and clopen OP00102.
It must not be nominated as unresolved or mistaken for MathDB362175.

Actual primary arXiv:2609.23520v1 (Shi–Zhang, 20 September2026),
Conjecture1.1 and the proof's Lemmas2.5 and2.10 and Section3, were read.
The proof writes a rectangular contraction as a finite convex combination
of isometries/coisometries and applies the classical square commutator
inequality. This establishes the full source inequality. The independently
posted Lean resolution of George Stepaniants (17 September2026) is also
listed at https://clopen.solutions/OP-00102/, with canonical statement matched.
The primary proof and registry page were saved; no upstream Lean replay
or absolute verification of either public submission is claimed here.

This bound does NOT by itself give the sharper weighted target362175:
putting B=W gives 2||W||_op^2||X||_(2,2)^2||Y||_F^2, whereas the open
target needs (w1^2+w2^2)||X||_F^2||Y||_F^2. The singular-value factor is
on a different matrix, with a different coefficient. No implication bridge
was found; this is a limitation, not a proof of logical nonimplication.

## 3. Alternating degree-three conjecture: bounded negative search

Laszlo's ELA38(2022)221–226 conjecture, restated literally in the actual
Li–Wang Mathematics14(2026)1548 primary body, asks for real matrices

 D=ABC+BCA+CAB-CBA-ACB-BAC,
 ||D||_F^2 <= (3/2) sum_cyclic ||A||_F^2 ||[B,C]||_F^2.

The known two-dimensional special cases are not new outcomes. A 2026
two-dimensional full-proof lead was located in the previous research lane
at Zenodo21506895, but no full-body novelty adjudication is based on it.
The all-dimensional claim is not resolved here.

alternating_search.py uses the exact linearization in A

    D=A[B,C]+[B,C]A+CAB-BAC

and the genuine quadratic denominator to solve a generalized Hermitian
eigenproblem in each factor in turn. Twelve operator identities were
cross-checked against literal multiplication. For n=2,3,4,5,6,8, twenty
starts per case, the largest found ratio is 1.5 to numerical precision,
both over real matrices (the source field) and complex matrices
(diagnostics only). No exact counterexample or proof was found. Results
are not used as a certificate or as novelty evidence.

## 4. Supporting observation: why the Frobenius-middle bound is easier

For arbitrary rectangular complex A,C of size m by n and B of size n by m,
vectorize ABC-CBA. After composing its input with transpose, the resulting
mn by mn matrix has entries

    S_(i,j),(l,k)=A_(i,k) C_(l,j)-C_(i,k) A_(l,j).

Therefore S^T=-S, and its squared Frobenius norm equals
2(||A||_F^2||C||_F^2-|<A,C>|^2). The standard unitary congruence normal
form for complex skew-symmetric matrices pairs all nonzero singular
values. Thus ||S||_op^2 <= ||S||_F^2/2, giving

 ||ABC-CBA||_F^2 <= ||B||_F^2 (||A||_F^2||C||_F^2-|<A,C>|^2).

The real-square version is already Laszlo's actual Theorem3.1. This
rectangular-complex argument is an elementary classical extension, not an
accepted discovery. It does not replace ||B||_F by its top-two singular-value
norm and so leaves weighted362175 open. No Lean formalization was started
for this helper. The skew identity is a direct index proof above, not an
inference from singular-value plots.

## Accounting

No additional credit from any computation or helper in this lane. All tests
completed normally; no process remains running. First thirty artifacts,
active Pi lanes, the frozen arcsinh review targets and Gamma definitions
were untouched. The accepted arcsinh result is tracked separately as
outcome31; it is not part of this matrix investigation.
