# H039 public-information operators: falsification and scope corrections

2026-10-08. Root synthesis of H039-information-grok-raw.md; independent
mathematical review by native Astra `/root/h007_additive_relations`. No numerical
experiment, executable import, new Lean claim or H034 cap reset. The following
is paper mathematics, not certified by the existing theorem audit.

## Decision

No operator is promoted. The named halving comparator fails as a universal
solver on an explicit synthetic curve. The consecutive-window procedure returns
already public parameters. No usable decoder advantage was established for the
short nonlinear statistics. These decisions do NOT establish a general barrier
against coordinate-aware or adaptive algorithms. Verified improvement NONE;
best supported exponent remains 1/2.

## Exact halving counterexample

Take E/F5: y²=x³+2x+1 and G=(0,1). Non-singularity follows from
4·2³+27·1²=59=4 mod5. The right-hand side at x=0,1,2,3,4 is respectively
1,4,3,4,3. Thus there are six affine points and infinity, and G has order7.
The multiples are

| k | [k]G |
|---|---|
|1|(0,1)|
|2|(1,3)|
|3|(3,3)|
|4|(3,2)|
|5|(1,2)|
|6|(0,4)|

Doubling G uses slope1, giving (1,3); adding G uses slope2, giving (3,3).
The remaining entries follow by negation. With iota=2^-1 mod7=4 and Q=6G,
A=[iota]Q=3G has x=3, while B=[iota](Q-G)=6G has x=0. The proposed rule emits
b0=1 although the canonical scalar6 is even. In its three-bit output range,
the possible odd integers are1,3,5,7; none is6 mod7. Final verification fails
whatever the later branch choices. Root and independent reviewer checked this
entire calculation by hand. This is a universal-correctness counterexample,
not a statistical scaling experiment or evidence about all branch predicates.

The raw assertion that ANY wrong bit forces failure is too strong. If
Q[j+1]=[2^-1](Q[j]-b[j]G), iteration gives
2^t Q[t]=Q[0]-(sum_j 2^j b[j])G. For K=sum_j2^j b[j], verification is K=k modq,
not necessarily K=k as integers. With t=ceil(log2 q) and 0<=K<2^t<2q,
K=k+q can also pass when it fits. A wrong first bit is fatal for
k>=2^t-q; the example satisfies this condition. No whole-chain success-density
bound is claimed.

Reflection k'=1-k modq swaps the two x coordinates. Away from their tie, the
comparison bits complement. For canonical2<=k<=q-1, k'=q+1-k has the same
parity as k. Hence the comparator cannot coincide everywhere with canonical
LSB. The fixed point k=iota requires separate tie handling. Again this proves
an exact-predicate obstruction, not a bound on modular output success.

Computing both halves from one scalar multiplication also needs a paid fixed-
half translation and its setup; the raw per-step ledger omits this cost.

Testing2G and3G can falsify exactness, but passing those two tests cannot prove
it. The raw rational-character argument does not apply to the named coordinate
order comparison without a further representation and Fourier bound. Its
conditional Fourier calculation therefore cannot replace the counterexample.

## Primary literature checked by root

[Mérai–Winterhof, arXiv:1509.06909v2](https://arxiv.org/html/1509.06909v2),
Sections2–3, Theorems1–2, freshly read. The first theorem has Edwards-model and
pole hypotheses. The second uses a nonconstant function in the coordinate
ring, degree below |G|^delta for fixed delta<1, and the multiplicative period t
of e modulo |G|. Its linear-complexity lower bound is proportional to
t/(|G|^(2/3) deg(f)^(1/3)), with delta-dependent constant. It is neither a
nonlinear-prediction impossibility theorem nor an index-recovery algorithm.
An odd prime-order subgroup alone does not exclude an ambient Edwards model;
that exclusion needs the whole rational group to lack the required torsion.

[Mérai, arXiv:1609.03305](https://arxiv.org/html/1609.03305), Theorem1,
Algorithm1, Remark1, and equations4–8, freshly read. Seven distinct consecutive
abscissae under the stated exceptional-point exclusions allow recovery of a
compatible recurrence over Q or Z/mZ. The unknown vector is
(xG,xG²,A,B,yG²,xG³); the scalar index is absent. Remark1 permits an arbitrary
window by replacing the initial point. This supports only the conclusion
that this displayed recovery system offers no new unknown for the present
ECDLP input, where the curve and G are public. It does not exclude other
uses of window algebra.

## Other rejected inferences

- The polynomial duplication aside mixes scalar field Fq with coordinate
  field Fp. A common field, compatible domain, denominator exclusions and
  enough zeros to force a polynomial identity are missing. The formal
  leading-coefficient calculation cannot justify the stated general condition.
- A bound for additive phases of x does not automatically bound a product
  of Legendre symbols against a multiplicative character of the scalar.
  No applicable theorem/bridge was supplied. Adaptive queries also require
  conditional hypotheses and complexity control; fixed-function bounds do not
  transfer automatically.
- A public function of Q can encode k; Q itself determines k uniquely.
  The missing issue is efficient extraction. Being public is no exclusion.
- H038's Fourier/RMS statements do not give a pointwise O(sqrt(p)) bound for
  every translated convolution. Autocorrelation at shift0 can be orderq.
- A dictionary restricted to T target-independent candidate scalars succeeds
  on at most T/q of uniform targets. Arbitrary feature-fiber search is a
  different model. Neither that bound nor the usual T+q/T schedule follows
  for every decoder without a specified output list or searchable structure.

## Next gate and record

No broad Lean infrastructure or additional run is warranted for these cards.
A new predictor would need an explicit public rule, a correctly scoped
whole-decoder success estimate and paid failures/verification. The surviving
H039 conditional hybrid cost region is separate: matched-memory and primary
prior-art reviews are live, and no experiment has been admitted.

Commands/evidence: root read the saved terminal task result; applied this
record with apply_patch; primary sources opened through web; mathematical
counterexample reviewed independently without a numerical tool. Validation
command for this checkpoint: ./scripts/check.sh >
/tmp/ecdlp-h039-information-check.log 2>&1. Record its exit status in STATE.md.
