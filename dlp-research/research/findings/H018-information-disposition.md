# H018 implicit relations: conditional recovery, no supplied signal

2026-10-08. Factory Opus r2 delivered one A-ALG candidate plus N1–N5 pruning
claims. Raw report retained in H018-information-factory-raw.md. Independent
native Astra /root/h007_additive_relations and root reviewed the mathematics.
No numerical campaign, piggyback rank computation or new Lean infrastructure
is admitted. Verified ECDLP improvement remains NONE.

## A-ALG survivor and corrected cost

Hypothesis: a nonzero R(N,Z) over Fq, bidegrees at most(d,e), vanishes at
(n,z([n]G)) for every nonzero scalar. For a KNOWN globally valid R, specialization
at z(Q) yields a degree-at-most-d polynomial containing the secret as a root,
unless the specialization vanishes identically. The gcd with X^q-X gives its
split squarefree part, not the roots themselves. Root enumeration/factorization,
randomness, specialization, retries and candidate scalar verification are paid.

At most e exceptional FEATURE values does not bound exceptional SCALARS for
arbitrary z: a constant feature and R=Z-c defeat every target. For the two
specified maps, integer reinterpretation has fibres at most ceil(p/q), x has
fibres at most2 and -x/y at most3 on admitted affine points. Thus exceptional
scalar fractions are bounded by2e ceil(p/q)/(q-1) and3e ceil(p/q)/(q-1).
The latter fibre bound follows by intersecting x+t y=0 with the cubic; the
t=0 case also has at most3. This repairs expected rerandomization only when
the applicable bound is small and points at poles/infinity are handled.

Full column rank of correctly labelled sample monomials is an exact finite
falsifier. A sampled kernel or64 holdouts is not a global identity certificate.
Under the STRONGER assumption of a pole-free rational representation with
numerator/denominator degree<=d,2d+1 distinct samples identify it uniquely:
the difference after cross multiplication has degree<=2d. Neither conditional
statement supplies a reason the named EC features have such representations.

With D=(d+1)(e+1),N=Theta(D), classical dense elimination costs O(D^3), so
sub-square-root setup requires D=o(q^(1/6)), before other costs. The raw q^.2
range requires an explicitly faster charged implementation. Memory O(ND),
sample generation and all preprocessing remain counted; many-target amortizing
is a separate problem statement. The raw campaign has no complete RAM ledger.

Implicit relations do extend beyond sparse powers, but overlap is substantial:
n^-1 already has geometric BM complexity1. Bounded-bidegree relations ARE
preserved under affine scalar substitution (with the missing-domain point
tracked); they form a nonlinear family, not an invariant linear subspace.
The raw claim of nonclosure is false. A planted nonconstant Möbius denominator
needs a pole rule; a denominator whose sole root is zero yields affine-plus-
inverse powers. A random-table failure cannot be a deterministic expectation.

No positive structural rationale was offered. Retain the precise hypothesis
without spending a new feature budget merely because another exact rank test
can be written. A new construction that predicts such a relation, with paid
learning and global validation, would change this decision.

## Pruning claims: accepted scopes and rejected inferences

N1: f(phi([n]G))=f([n]phi(G)) for a fixed homomorphism is exact. A codomain
bound transfers only with its actual field/feature/character hypotheses and
nonzero image generator. This does not bound correlation with ANY scalar
function, adaptive maps, or multi-view nonlinear constructions.

N2: reject the proposed nonalgebraic-or-CDH dichotomy. A correspondence's
Jacobian homomorphism does not make each pointwise branch affine on logs.
For example x(S)=x(P)+1 has square-root branches when admissible, summing to O;
the individual branches need not be homomorphisms. This is a counterexample to
the inference, not an attack. Scalar maps can have small order on a finite
subgroup without being curve automorphisms; evaluation cost matters. A known
bounded-degree scalar-polynomial oracle can imply CDH via finite differences
under suitable characteristic/degree assumptions, not for arbitrary formal
degree or all cheap maps.

N3: full Fq-valued functions on Fq under translation form one Jordan block;
invariant subspaces are the polynomial-degree flag. On Fq*, dilation
eigenfunctions are monomials. These global representation statements do not
classify finite-prefix ranks, noisy/nonlinear/vector features or every spectral
algorithm. Parseval needs an actual feature-specific Fourier bound, including
the constant coefficient; the blanket plus/minus-one feature claim is rejected.

N4: reject area<p =>O(1) points in a scalar/coordinate box. A small main-term
expectation is not a discrepancy bound. No supplied occupancy theorem or
landmark-dictionary reduction justifies this closure.

N5: repaired exact lemma. Let p>3, R in E(Fp) have odd prime order q, and
gcd(q,p-1)=1. Choose positive N with N=1 modq and N²=1 mod(p-1). Division-
polynomial composition, applied in both orders and cancelling nonzero factors,
gives psi_N([m]R)=psi_N(R)^(m²) whenever q does not divide m. Put A=psi_N(R).
Compare m=1 and2 with m+q: A^(q(q+2))=A^(q(q+4))=1. Their exponent gcd is q,
so A^q=1; coprimality implies A=1. The raw single-comparison q² step was
invalid. This proves constancy on the nonzero rational order-q subgroup only,
not a function-field identity or closure of normalized/twisted EDS variants.
The composition and nonvanishing facts were checked in §1/Lemma2 of
[Shparlinski–Stange](https://arxiv.org/pdf/0912.5246); the deduction here was
independently checked by root and Astra. No Lean formalization claimed.

## Primary-source scope

Root read §3/Theorem1 of the author-uploaded
[Lange–Winterhof paper](https://www.researchgate.net/publication/221427032_Polynomial_Interpolation_of_the_Elliptic_Curve_and_XTR_Discrete_Logarithm).
It bounds degrees of base-field polynomials of x encoding scalar indices on
interval subsets, using addition formulas. It does not directly cover the
mixed-modulus implicit relation here. Bibliography confirmed on the
[author page](https://www.hyperelliptic.org/tanja/publications.html).
Root read only the author-institution
[Coppersmith–Shparlinski abstract](https://researchers.mq.edu.au/en/publications/on-polynomial-approximation-of-the-discrete-logarithm-and-the-dif/):
finite-field multiplicative-group polynomial/algebraic approximation bounds.
No full-text theorem from it is imported into this EC mixed-modulus setting.
Raw memory-only citations remain unverified unless explicitly checked above.

Best work remains the accepted square-root reference with known constants;
verified gain NONE. Next useful step is a concrete signal/detector construction
or complete-cost improvement, pursued by independent H019 roles. The exact
finite BM diagnostic is separate and has no A-ALG test appended.
