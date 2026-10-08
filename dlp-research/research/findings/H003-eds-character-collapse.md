# H003: fixed-window EDS predictor reduces to a bounded coordinate character

**Accepted paper-level negative finding:** for a fixed or polylogarithmic number
of offsets on a large ordinary prime-order subgroup q≈p, A1 cannot supply the
bias magnitude used by H003's conservative sub-square-root sufficient bound.
This closes that proposed fixed-window route, not arbitrary coordinate-aware
algorithms or all EDS uses. No improved ECDLP algorithm has been found.

Native Astra `/root/h002_arithmetic_ideas` proposed the identity and source
application. Independent Claude Opus reviewed the mathematics and main source.
Root separately retrieved the primary antecedent to resolve defective wording,
checked the divisor argument and qualified the review's overextensions below.
No new field experiment or Lean theorem was used. Prior capped data remain intact.

## Exact character simplification

Use a smooth short Weierstrass curve over Fp, p>=5, an odd prime subgroup
<G> of order q>=5, and gcd(q,p−1)=1. Let chi be the quadratic character.
For nonidentity points the already corrected normalization satisfies
`phi(2T)=phi(T)^4*W_T(2)=phi(T)^4*2y(T)`.
All factors are nonzero on this odd subgroup. Consequently
`chi(phi(R))=chi(2y([2^-1 modq]R))`.

For distinct offsets A modulo q, s=|A|>0, put H=[2^-1]G. The diagnostic's
fixed product, zero at identity windows, is exactly
`B_G([k]G)=chi(f_A([k]H))`,
where `f_A(S)=2^s*product_(j in A) y(S+[j]H)` and poles are assigned zero.
Using S=kH is essential: division by2 on the finite subgroup must not be treated
as a globally rational inverse to the elliptic doubling morphism.

Over the algebraic closure, y has simple zeros at the three nonzero2-torsion
points and a pole of order3 at O. Distinct translates by jH have disjoint
2-torsion cosets: their difference lies both in the odd-q subgroup and E[2]
only when the offsets agree. Thus no zeros or poles cancel, f_A has pole degree
3s and simple zeros, and is not a constant times any proper power even after
extending constants. Its poles in <H> are precisely the s omitted windows;
none of its zeros lies in <H>.

## Primary theorem and normalization

[Chen, Elliptic curve analogue of Legendre sequences (2008)](https://www.researchgate.net/profile/Zhixiong-Chen-8/publication/225752100_Elliptic_curve_analogue_of_Legendre_sequences/links/542eab7e0cf27e39fa963730/Elliptic-curve-analogue-of-Legendre-sequences.pdf),
Proposition1, printed p.4, supplies a mixed elliptic-group/multiplicative-character
bound of 2*deg(f)*sqrt(p); its definition omits zeros and poles. It explicitly
uses proper powers l>1. Root and Astra retrieved this primary paper. Its degree
convention gives deg(x)=2, deg(y)=3. Our simple-zero check meets the stronger
geometric nonpower condition, without relying on constant nonsquares.

[Shparlinski–Stange, Character Sums with Division Polynomials](https://arxiv.org/pdf/0912.5246),
Lemmas4–5, state the bound and derive the subgroup version by averaging characters
trivial on the subgroup. Their field-size symbol q is our p. Their literal
'algebraic closure of K' and inclusion of m=1 are defective wording: every element
has roots in a full algebraic closure of a function field. Use the geometric
nonpower condition over the constant extension, with proper powers, as checked
above. Do not quote that defective sentence as a literal usable hypothesis.

Every character of <H> extends to the finite abelian group E(Fp). Applying the
subgroup average and the degree bound gives, for normalized Fourier transform,
`|hat(B)(a)| <= 6*s*sqrt(p)/q` for EVERY a in Zq, including zero.
The missing identity windows contribute zero, so normalization is exactly q.
Combining with the canonical parity transform's l1 bound <=2+ln(q) gives
`|q^-1*sum_k B_G(kG)*(-1)^k| <= 6*s*sqrt(p)*(2+ln(q))/q`.
These displayed consequences and divisor application are our derivation; the
papers provide the general character theorem, not a new ECDLP claim.

## Consequences and boundaries

For q≈p and s fixed or polylogarithmic, all amplitudes are q^(-1/2+o(1)) and
parity correlation is at most q^(-1/2+o(1)). This cannot satisfy the sufficient
epsilon=q^(-beta), beta<1/12 regime of the explicit epsilon^(-6) construction.
It also removes the proposed escape of an unrelated large Fourier coefficient
within the SAME fixed-window product. A failing sufficient bound is not a lower
bound for every recovery algorithm; do not claim a generic hardness proof.

The conclusion holds for both chi(phi(G)) signs, odd/even windows and CM curves.
The small diagnostic's correlations are compatible with the theorem, whose
constants are weak at tiny q. No post-hoc winner can override the bound, which
is uniform over choices of distinct offsets of the same size.

The mathematics permits q=p, but anomalous curves are outside the ordinary-hard
target assessment. It also permits odd prime subgroups of some supersingular
curves: the review's blanket claim that supersingular curves are automatically
excluded by even total order is false for subgroups, and is NOT adopted.
If q is much smaller than p, retain the actual sqrt(p)/q factor; no q≈p inference.

Large growing windows are NOT closed. The stated bound weakens with s and can
become trivial. A high-degree product could conceivably have a compact evaluation
circuit; polynomial degree alone is no runtime lower bound. No such useful
construction or full-work gain is supplied here. The full set A=Zq makes every
input an excluded window, hence B=0, not a useful nonzero constant predictor.

For a fixed Boolean function of s window bits, Walsh expansion offers an
extension with its coefficient l1 norm and identity-window correction. It is
NOT automatic that s=O(log q) remains harmless: that norm can be as large as
2^(s/2). The review's blanket extension to learned selectors/majority at that
size is not adopted. Adaptive queries, non-character features, stateful rules
and other EDS functions remain outside the proved product-family statement.

## Research decision

Archive the fixed-window A1 bias hypothesis as analytically unfavorable for
the proposed reduction. Do not spend a larger diagnostic budget or implement
Fourier numerical machinery for it. Keep the exact normalization correction,
incomplete finite data, prior uncertainty and failed guesses. This was a useful
negative result, not an improved attack or new character-sum theorem.

Separate p-adic carry/section hypotheses have concrete formulas but no established
concentration mechanism; their independent review is live. Reopening A1 requires
a genuinely different feature/large-window mechanism and matched complete cost,
not more seeds for the same fixed products. No hardware/GPU extrapolation.
