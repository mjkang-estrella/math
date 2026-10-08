# H029 arithmetic transport: no new surviving operation

2026-10-08. Native Sol independent initial lens COMPLETED, no numerical work,
imports, edits or other H029 proposals used. Root checked the recovery maps and
base-field restrictions and opened the primary sources below. This is a scoped
no-survivor report, not an impossibility theorem. Improvement NONE.

## Small isogeny transport to a=-3

For an explicit rational isogeny phi of degree coprime to q, its restriction to
the q-subgroup is injective. Solving phi(Q)=d*phi(G) recovers the original d,
which is independently verified by dG=Q. A bounded small-degree search followed
by rescaling may produce a=-3, but degree/kernel search, failed attempts, maps,
jump setup, memory and all later arithmetic are paid.

[Brier–Joye, Fast Point Multiplication on Elliptic Curves Through Isogenies](https://marcjoye.github.io/papers/BJ03isog.pdf),
§§2–5, describes known transport and faster a=-3 projective doubling. It does
not establish an improved search schedule for this proposal. In the matched
affine addition and H019 side-generation kernels, the curve coefficient does
not enter ordinary additions. A saving on D doublings of D*DeltaCdbl needs a
named full search with enough such doublings to overcome transport and changed
representation costs. No favorable schedule was supplied. Full prime order does
not forbid rational odd-degree isogenies with non-pointwise-rational kernels.

## Extension-field Montgomery coordinates

Let f=X³+AX+B. Full odd group order means f has no Fp root, hence it is
irreducible cubic. Over Fp³ choose a root r, and over at most a further quadratic
extension choose c²=f'(r). Nonsingularity gives c!=0. Substitution x=r+c*u,
y=c*v yields

    c^(-1)*v² = u³ + (3r/c)*u² + u.

Root verified this expansion directly. This is an extension degree3/6 interface,
not a base-field Montgomery conversion. Labels and recovery survive the map.
[Morain, Edwards curves and CM curves](https://arxiv.org/pdf/0904.2243), §2.4,
gives the relevant model conditions; proposer also read its torsion discussion.

An actual gain needs a cheaper complete successor/key primitive after extension
construction, roots, maps, arithmetic, normalization, traffic and recovery.
Known-difference differential addition is not arbitrary r-adding. Conversely,
extension degree alone does NOT prove loss: image coordinates lie in fixed
Fp-affine lines and may compress. The decisive next operation would be an
explicit substitution into a named successor and actual base-field ledger.
None was derived, so constructing an extension engine is not admitted.

## Complete homogeneous formulas

[Renes–Costello–Batina, Complete addition formulas for prime order elliptic curves](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/06/complete-2.pdf),
Table3 and §5.3, supply established complete formulas and implementation context.
The general mixed-addition ledger cited by Sol is11M+3m_a+2m_b+17A. Completeness
may reduce exceptional control; it does not add scalar coverage. Projective state,
canonical partitions/keys, table normalization, cycle handling and verification
still cost work. Hashing arbitrary projective triples is not a point-invariant
successor rule. No complete saving against competent mixed/projective and
batched-affine alternatives was supplied.

Disposition: no experiment for these literal constructions. Reopen only with the
missing cheaper operation and matched full-cost premise. Known primitive formulas
or valid transport alone are not algorithmic research gains. Generic exponent
reference remains1/2. No new Lean/Audit claim.
