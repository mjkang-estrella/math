# Statement correspondence after locality repair

The source is Tully-Doyle–Adlin–Thai–Tiscareno, arXiv:2410.10695,
Conjecture 6.1 (MathDB 365301). This lane repairs the formal correspondence
identified in contact-review-r2, Gate A. It does not perform a new novelty
search or claim acceptance. The source-body review and its bounds are retained
byte-for-byte under inputs/contact-review-r2. All 28 r5 modules, including
SourceContact.lean and its old predicates/endpoints, remain byte-identical.

| Source concept or obligation | Formal declaration | Correspondence |
| --- | --- | --- |
| Local numerator zero set at a named torus point | HasLocalZeroSetContact | Unit norms and boundary zero; one positive lower neighborhood; uniform positive c and C; upper witnesses in every smaller positive neighborhood, with a possibly smaller parameter interval |
| A single contact order | local_contact_unique | For arbitrary q and unit point, any two natural-number orders satisfying the repaired predicate are equal; no polynomial, parity, positivity, or certificate assumption needed |
| Universal graph assertion | SourceConjectureLocal | Identical quantifiers and hypotheses to SourceConjecture, replacing only its contact predicate |
| Genuine graph function | candidateCertificate | Actual five-vertex resolvent, reduced stable pair, coefficient reflection, phase 1, bidegree bounds (3,2), equality throughout open bidisk |
| Distance to nearest w vertex | nearest_w_one | Attained walk distance 1, and every walk to a w vertex has length at least 1 |
| All roots approach the correct point | R_roots_localize; numerator_images_localize | Inherited arbitrary-neighborhood root localization; lower-half-plane roots approach 0, their Cayley images approach 1 |
| Upper bound in any prescribed neighborhood | parameterized_contact_six_localized | New strengthened real-parameter comparison, arbitrary ε > 0, same lower constant 1/8 and upper constant 16 |
| Contact at (-1,1) | bidisk_local_contact_six | HasLocalZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6, unconditional |
| Predicted contact 2 impossible | bidisk_not_local_contact_two | Immediate from local_contact_unique and contact six |
| Literal repaired endpoint | refutationLocal | ¬ SourceConjectureLocal; specializes universal assertion to d = 1, K = 6 and derives 6 = 2 |

The new predicate follows the root ruling exactly. In particular c, C and rho0
are chosen before rho; C cannot vary with rho. The lower clause applies to
every disk zero inside rho0 after one delta0. The upper clause produces a zero
inside every rho ∈ (0,rho0] after its own delta. It cannot import a different
boundary cluster by enlarging a single existential radius. No isolation,
polynomial degree, branch matching, or candidate-specific hypothesis is added
to the universal assertion. The inherited half-plane predicate is historical;
the new endpoint relies on the stronger localized theorems.

The uniqueness proof combines the K1 lower bound with the K2 upper witness
inside the intersection of their neighborhoods. If K1 < K2, cancellation of
the positive displacement power contradicts C2 h^(K2-K1) → 0. The unit circle
has punctured points arbitrarily near every unit point, proved using the real
Cayley chart. This handles K = 0 as well as positive orders.

The five-vertex proof reuses the old lower estimate with its fixed neighborhood
and localizes the upper witness using half_plane_contact_six_localized with
min(1/8, ε/4). The Cayley estimates preserve uniform upper constant 16.
The real circle chart supplies all nearby unit-circle z, not a subsequence.

The source's claimed relation is contact order K = 2d. Restricting its universal
claim to existing finite nearest-w distances, certified reduced pairs, and
positive even contact orders only weakens that claim. The witness has distance
1 and positive even order 6, so these restrictions do not evade the conjecture.
This argument now uses a genuinely local contact hypothesis; it was not valid
to justify the former non-local predicate just by calling it a restriction.
No general equivalence theorem to every possible analytic definition in the
literature is claimed. The inherited source review identifies the local maximum
branch convention, and the finite analytic branches of this witness give that
maximum, 6. The lower-for-all and upper-for-some comparisons express precisely
the corresponding infimum radial-height order.

REGRESSION.md supplies an ordinary proof that the reviewer's diagnostic pair
has repaired local order 2 and cannot have 6; scripts/regression.py checks its
exact algebra. This optional diagnostic is not formalized in Lean.
