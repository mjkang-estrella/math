# R026 — An integral regular summand in every staircase Specht tensor cube

**Accepted as the fourth substantial result of the 2026-10-14 ten-additional
campaign.** This is internal research acceptance after separate proof,
contribution, manuscript and scoped formal reviews. It is not external peer
review, an exhaustive priority determination, or a public submission. The
integral and every-ring conclusions constitute one result.

## Exact theorem

For every integer m >= 1, put N=m(m+1)/2, rho=(m,m-1,...,1),
B={(i,j): i,j>=1, i+j<=m+1}, and G=Sym(B). In the common word realization
of the integral Specht lattice S_Z^rho, define v_R and v_C by alternating
the letters 1,...,r on each row and column of length r, respectively.
Rows are ordered left to right and columns top to bottom, as specified in
Section 2 of the paper. Set L=(S_Z^rho) tensor (S_Z^rho) tensor (S_Z^rho)
and z=v_R tensor v_R tensor v_C, with diagonal left G-action.

The map I: Z[G] -> L given by delta_g -> gz has an explicit integral
G-linear left inverse P. Thus its N! orbit vectors form a basis of a split
regular summand. For every commutative unital ring A, including nonflat
extensions and the zero ring, the scalar-extended maps give a split
A[G]-embedding into (S_A^rho) tensor_A (S_A^rho) tensor_A (S_A^rho), where
S_A^rho=A tensor_Z S_Z^rho. No factorial is inverted and no characteristic
restriction is imposed.

Explicitly, let beta(i,j)=m+2-i-j, b0(i,j)=j, and let theta* extract the
coefficient of (e_beta,e_b0,e_beta) in ambient tensor-word coordinates.
Then

    P(x) = sum_(g in G) theta*(g^(-1)x) delta_g.

The paper proves that this agrees on every basis triple with
J^(-1) pi_D q^B, where q(a,b,c)=0 unless a=c and otherwise returns the
letter (a+b-1,a), D={(r,a):1<=a<=r<=m}, and J identifies the distinct-letter
orbit with the regular module. The surviving term has coefficient +1.
The theorem supplies lower bounds on regular multiplicities, not exact
multiplicities of the entire tensor cube.

## Proof, sources and contribution boundary

The complete [six-page manuscript](../campaigns/2026-10-14/staircase-manuscript/main.pdf)
has PDF SHA256 `40aebbdda3c407298f499895b7cd8aee543025864efbcb94808441e1b6b6f54c`
and TeX SHA256 `015e76c58ebbd6b92c8868d2de9cf49f533f18408e5017b720df8d02f4767495`.
It proves the integral polytabloid identification, equivariance, coordinate
formula, integer square-deficit support elimination, palette induction,
positive unit sign, splitting and arbitrary base change as a standalone
argument.

Bryant–Kovács' separating-product mechanism, Ikenmeyer's triangular
uniqueness, and the pinned cyclic-polytabloid square-deficit construction
are credited ingredients. The new conclusion is the integral and
every-characteristic regular summand. Complex regular containment is an
antecedent from the pinned complex surjection and Harman–Ryba, or from
I21's stronger intermediate isomorphism and Harman–Ryba. Characteristic-2
projective-indecomposable occurrence is also already known. These are not
additional contributions, and the specified generator alone earns no
separate novelty claim.

The contribution review judges the package SUBSTANTIAL narrowly within
its recorded primary-literature comparison, particularly for regular
multiplicities and the unrestricted positive-characteristic conclusion.
It makes no worldwide-priority guarantee. OpenAI inputs are accepted at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; the paper reproduces the integral
arguments and does not use complex constituent coverage to infer modular
splitting. It does not transfer field-level injectivity of the regular
module to the integers.

## Independent gates and validation

- [Proof review](../campaigns/2026-10-14/staircase-proof-r1/review.md): PASS
  for the full original all-m and every-ring theorem, with no repairs.
- [Contribution review](../campaigns/2026-10-14/staircase-contribution-factory-r1/review.md):
  SUBSTANTIAL narrowly, with attribution requirements implemented in the paper.
- [Full manuscript review](../campaigns/2026-10-14/staircase-manuscript-review-r1/review.md):
  PASS with no paper edits required, SHA256
  `2b9d5470d96c0f334eed1073489b94c13296fea12924acb096fdb26850184d76`.
- [Scoped Lean review](../campaigns/2026-10-14/staircase-formal-review-r1/review.md):
  PASS with no repairs, SHA256
  `92b21ed40425c72be41c00a4eb65e2d349b33e8dfeffe3bbb930067cbe30b254`.

The parent authenticated the reviews and frozen paper, read the complete
manuscript and checked every rendered page. The independent manuscript
review rebuilt a byte-identical PDF and added nine finite control groups;
the parent reproduced their complete receipt on a copy. These cover
polytabloids, projection, the orbit identity, coordinate equivalence,
palette and deficit checks, hook divisibility, the complex antecedent and
mutations. Such finite tests support the proof; they do not prove all m.

Both final-package conditions are satisfied: the full cited I21 note is
included at its exact hash with a rights notice, and an actual scoped
formal-coverage supplement explains the completed audit and omissions.
Ten optional editorial clarifications are embedded in the included parent
disposition without changing reviewed manuscript bytes.

## Formal coverage and release

**The full staircase theorem is not formalized in Lean.** Sixteen supporting
theorems prove the conditional finite-group coordinate splitting and its
equivariance, injectivity and invariant complement, scalar extension of
given split/intertwining maps without flatness, and the integer zero-deficit
implication. The staircase-specific separation identity is an explicit
unproved instance, not a formalized theorem. Polytabloids, palettes, support
budget, positive unit sign, the all-m instance and multiplicity conclusions
remain prose proofs. The independent audit adds eighteen review theorems,
including noncommutative and nonflat examples, and rejects three source
mutations. Fresh-source compilation uses Lean 4.34.1 and pinned mathlib
with only standard axioms; dependencies and compiler remain trusted setup.

Author: **Myeongjin Kang**, no affiliation. Original prose CC BY 4.0;
original code MIT; third-party notices retained. The [release workflow](../campaigns/2026-10-14/staircase-release/README.md)
prepares local Zenodo/MathDB drafts and reproducible source materials.
Earlier pending/count fields in frozen preparation records are historical.
This acceptance record and the included final parent disposition supply
the later state. No DOI, public paper URL, MathDB record or external
endorsement is claimed.

The verified local archive is
`output/release/r026-integral-staircase-regular-summand-v1.zip`,
1,085,619 bytes, SHA256
`c371bc4461d5c40b701e3f5445ccd664a1c8f8184b537544a117f2b73c92f42b`.
It contains 172 project files plus its bundle manifest. Clean extraction
verified exact inventory and review bindings, the frozen formal audit,
two historical finite programs, 3,072 interface comparisons and all nine
independent manuscript control groups without modifying the extracted tree.
See the [final receipt](../campaigns/2026-10-14/staircase-parent/final-package-verification.json).
Nothing has been publicly uploaded or submitted.
