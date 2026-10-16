# R024 — Disk rigidity for attained complete polynomial equality

**Accepted as the second substantial result of the 2026-10-14 ten-additional
campaign.** This is internal research acceptance relative to the stipulated
pinned OpenAI inputs and credited geometric theorems, not external peer
review, a worldwide-priority certificate, or a public submission. The
channel, inverse and disk conclusions are accepted as one result.

## Exact theorem

For every finite n,m>=1, every complex n by n matrix A, and every matrix
polynomial F(z)=sum_(k=0)^d z^k C_k with complex m by m coefficients and
arbitrary finite degree, use Euclidean operator norms and the base-first
evaluation F[A]=sum_(k=0)^d A^k tensor C_k. Set

    M = max_(z in W(A)) ||F(z)||.

If M>0 and ||F[A]||=2M, then W(A) is a nondegenerate closed disk.
No rank-one, simple supporting eigenvalue, initial boundary smoothness,
initial irreducibility, or dimension bound is imposed.

Normalize F by M. For every irreducible reducing block B attaining two,
there are fixed coefficient subspaces E,G of the same positive rank r,
isometries U,V onto them, and a polynomial J(z)=V*F(z)U such that F(z)E
is contained in G for every complex z and J is unitary on the boundary
of K=W(B). Its inverse Q is rational, holomorphic throughout the exterior
of K, continuous on its boundary, and tends to zero at infinity. The
nonconstant polynomial f=det J satisfies both full level identities

    {z: |f(z)|<1} = interior K,    {z: |f(z)|=1} = boundary K.

These conclusions do not assert a scalar coefficient compression of the
specified witness. Arbitrary rational or holomorphic witnesses,
nonattained complete suprema, quantitative gaps, stability, and a
classification of disk matrices are outside the claim.

## Proof and contribution

The full proof is the [11-page manuscript](../campaigns/2026-10-14/matrix-disk-manuscript/output/pdf/main.pdf).
PDF SHA256: `ec3b4818c147ae4fefcf9c46760a2a621e1503e3ea025cbbf748405f379eaa8a`.
TeX SHA256: `e90c6cb16bc5bbce03eeaebfd8d8f5c17f77059985a41c7404478db80a2ce609`.
Its source map distinguishes stipulated operations, reproduced inherited
arguments, new deductions, and credited geometric inputs. Preparation-time
status text is preserved to keep every reviewed byte unchanged; this record
and the later parent dispositions state the integrated decision.

The manuscript reproduces dimension-independent exterior boundary
convergence and residual extraction from the earlier equality mechanism.
The new argument retains the Jensen deficit in finite diagonal dual tests,
taking the finite-test limit before the moving-domain limit. A triple
Hilbert-valued variance identity and Fatou then force the diagonal fields
to be constant. Positivity on a curved boundary arc supplies the needed
strictness without limiting marginal identities or a uniform spectral gap.

Trace rationalization gives a denominator with no exterior or boundary
zeros. The residual Gram system has arbitrary positive rank. An ordered
constant test and equality in Parseval produce fixed coefficient spaces
and the full boundary channel identity. Restricting before inversion gives
Q=(1/2) S_E^(-1) U* Mcal^T V, with the ordinary transpose and the indicated
left Gram inverse. Its decay gives the entire determinant sublevel set,
excluding extra exterior components. Noncriticality and the Hermitian
tangent determinant pay the full interface of Jin's circle criterion;
convex polynomial lemniscates alone are not claimed to be circles.
The resulting determinant monomial confines inactive reducing blocks to
the same disk, restoring the full original numerical range.

R016, its dimension-five technical continuation, and the rank-two disk
witness R019 are antecedents. The new arbitrary-rank bridge extends beyond
their scalarization range. Jin's scalar rigidity and the ACV complete
dimension-three result are separately credited. The contribution review
classifies the entire package as SUBSTANTIAL after a bounded primary-source
comparison; it does not establish universal novelty or priority.

## Independent gates and validation

- [Full proof review](../campaigns/2026-10-14/matrix-disk-proof-r1/review.md):
  PASS, no required repair. SHA256
  `c1b09f8ad9d05d4b0d323079871b4cfb1e0f2084b41b6e5b0d07f8029288c6c7`.
- [Separate contribution review](../campaigns/2026-10-14/matrix-disk-contribution-r1/review.md):
  SUBSTANTIAL for one package, bounded coverage. SHA256
  `d317e565614f3babf2c03e5c6e7b5f4980c31ab28f7e2059b01adc1c8f932df5`.
- [Fresh manuscript review](../campaigns/2026-10-14/matrix-disk-manuscript-review-r1/review.md):
  PASS for every original quantifier and the stronger active-block package;
  no required mathematical or layout repair. SHA256
  `35f67ec7bd5d885c4ccd2c2230d694faaa85eb5fa5657ae828b21e91b9a99ce0`.

The parent read the complete proof/manuscript reviews and manuscript,
checked the source interfaces and frozen hashes, reproduced the 17+16
exact supporting checks, and inspected all eleven PDF pages. The final
review separately reconstructed the proof, checked 52 source-map line
targets, reproduced the finite checks and inspected every page. An
optional scalar-maximum/zeroth-coefficient notation collision is harmless
in context and is documented rather than changing the frozen paper.

The pinned input revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
The complete inequality and Faber operations are stipulated true. Jin's
Lemma 8 and Proposition 6 are credited external inputs with their exact
interfaces stated, not new theorems of this package. The paper and source
map expose these dependencies.

## Publication and formal coverage

The [local release workflow](../campaigns/2026-10-14/matrix-disk-release/README.md)
packages the reviewed PDF/TeX, provenance, independent reviews, exact
checkers, all-page QA, and a portable hash/check verifier. Its archive
receipt records clean-extraction verification. Author: Myeongjin Kang,
no affiliation; original prose CC BY 4.0, original code MIT. Third-party
rights are preserved. Historical third-party source copies are excluded.

**No full Lean certificate exists.** The 33 exact finite checks exercise
Gram restrictions, inverse multiplication order, transpose and half
factors, and variance orientation, including deliberate mutations. They
do not establish the conformal, Hilbert-valued, Fatou, rationalization,
maximum-principle or geometric arguments. GLM's finite real scalar variance
implementation has now passed the [independent parent audit](../campaigns/2026-10-14/matrix-disk-formal-review-r1/review.md).
The generic identity, per-column identity and nonnegative-deficit corollary
compile on Lean 4.34.1 and pinned mathlib with only propext, Classical.choice
and Quot.sound. A [portable Lake project](../campaigns/2026-10-14/matrix-disk-formal-v1/README.md)
and exact source/audit receipts supplement the updated archive. This does
not retroactively supply a formal proof of the analytic argument and earns
no separate accepted-result credit.

Nothing has been submitted to Zenodo or MathDB. The local MathDB routing
draft distinguishes this equality theorem from the credited complete
inequality in record 392465. No public URL, DOI or endorsement is invented.
