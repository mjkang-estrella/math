# H046 small non-rational isogeny: deterministic subfield-filter bound

2026-10-09 UTC. Status: independently checked paper result, not Lean-certified.
Best supported ECDLP exponent 1/2; verified complete-work improvement **NONE**.
This corrects Card B of H046-operators-factory-raw.md. No experiment is needed
to replace its unsupported uniform-image and genus-two counting assertions.

## Exact scope and proof

Let E/Fp be an elliptic curve, p>3, and G in E(Fp) have odd prime order q.
Let phi:E -> E' be an origin-preserving separable isogeny defined over Fp²,
of odd prime degree ell distinct from p,q. Fix Weierstrass coordinates on E'
over Fp². Assume its kernel K is not stable under p-power Frobenius on E.
Consider nonidentity points P in <G> for which x(phi(P)) belongs to Fp.
There are at most **4ell** such points (or q-1, if smaller).

Write x(phi(P))=r(x(P)), r=N/D with coprime polynomials over Fp² and
max(deg N,deg D)=ell. The rational-x representation and degree formula are
standard: [Galbraith, Chapter 9, Lemmas 9.6.12–9.6.13](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf).
The following polynomial argument is the root derivation reviewed independently
by native Astra; it is not attributed as a theorem stated in that source.

Let sigma conjugate COEFFICIENTS by z -> z^p, leaving the indeterminate X fixed.
For x in Fp with D(x) nonzero, r(x) lies in Fp exactly when

    H(x)=0,    H=N D^sigma - N^sigma D.

The degree of H is at most 2ell. It is not the zero polynomial: otherwise
r=r^sigma, so the pole divisor of r(x) as a function on E would be
Frobenius-stable. But r(x)=x composed with phi has poles precisely at the
kernel K, since the target x-coordinate has its only pole at the target
identity. Stability of that pole divisor forces stability of its support K,
contradicting the hypothesis. Thus H has at most 2ell roots in Fp; each
abscissa lifts to at most two source points. This proves the bound.

The q-subgroup has no nonidentity kernel point because ell differs from q.
Its nonidentity points therefore avoid these poles; the source identity maps
to infinity and is handled separately. On this subgroup phi is injective,
and phi([k]G)=[k]phi(G), so no scalar relation was lost in the transfer.
The argument needs neither a random distribution in E'(Fp²) nor a claim that
j(E') is outside Fp. It holds for each fixed allowed target coordinate model.
Changing coordinates cannot defeat the pole-support argument while retaining
these hypotheses; arbitrary non-Weierstrass feature maps are outside its scope.

## Construction assumptions and implication

If an available small odd prime ell divides the Frobenius trace t and ell!=p,
the characteristic equation on E[ell] gives pi²=-p. Hence every line is stable
under pi²; a line not stable under pi yields a kernel defined over Fp² but
not Fp. The existence of such a line and a suitable small trace divisor must
be checked. Kernel stability over Fp² does not imply that its individual
points are Fp²-rational. Finding a kernel, representing any larger extension,
constructing the quotient/isogeny, evaluating it and extracting relations all
remain paid. A general necessity claim about ell|t is not proved here.

For fixed small ell, the proposed subfield filter has density at most 4ell/q
on the original subgroup. This removes the suggestion of importing a dense
ambient subfield filter for free. It does not establish an algorithmic lower
bound for all uses of isogenies. For growing ell the result is an O(ell)
cardinality bound, not a runtime floor: compact evaluation and any relation
search still require their own algorithms and success/cost analysis. The raw
"about two" expectation and unproved O(sqrt(p)) genus estimate are withdrawn,
as is any conclusion obtained by inserting those estimates into a join price.

## Process, objections, validation

Original proposer: Factory claude-opus-5-5, task
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h046-primary-public-operators-factory-opus-20261009-r1`.
The complete raw output and unusual backing-thread retrieval are retained in
H046-operators-factory-raw.md. It used archive pointers, not new primary reads,
and disclosed reading H046-half-orbit-evaluator.md; do not label it wholly
unexposed to this wave's work. Root proposed the bound above after source
review. Native Astra /root/h007_additive_relations independently checked the
coefficient-conjugation, pole-support argument and subgroup exceptions; final
review completed. Native Sol separately reviews costs of all algebraic cards.

Root read Galbraith Chapter 9, especially 9.6.12–9.6.19, before integration.
No numerical run, import, new instance, Lean claim or Audit addition. H034's
consumed cap remains unchanged. The exact project check is in STATE; it checks
existing formal artifacts and does not certify this paper result. Reopening
requires an explicit changed public filter or a paid growing-degree algorithm
with a complete recovery advantage, not an ambient random-image assumption.
