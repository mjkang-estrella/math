# H027 automorphism-compatible repair and genus-character interface

2026-10-08. Two distinct native tasks completed during the still-live Grok/Fable
initial roles. Astra proposed an explicit pairing-orbit construction; root checked
the finite cyclic-group identities and cost distinctions. Sol inspected the actual
CSV primary manuscripts and tested their hypotheses; root independently checked
the discriminant and Frobenius-rank calculations. No experiment, implementation,
Lean theorem or improved full solver is claimed.

## A computed symmetry-compatible object, with known recovery cost

Let lambda have order3 modulo q and U=<-1,lambda> of order6. The formal scalar
character chi_q(1+k^6) respects these known symmetries but is not an extraction
algorithm, nor proved constant on every unmarked surface-isomorphism fibre.

An actual public computation uses the existing pairing representation. For
r=ord_q(p), construct L=Fp^r and a nonzero p-Frobenius eigenvector H in E[q].
Certify its torsion and nontrivial pairing zeta=e_q(G,H), then z=e_q(Q,H)=zeta^k.
The explicitly formed polynomial

`P_Q(T)=product_(u in U)(T−z^u)`

is invariant under k→uk and separates exactly these scalar orbits: equal root
multisets mean k'U=kU. Q=O is handled separately. This is an invariant of the
pairing representation, not of every unmarked surface presentation.

Given the polynomial alone, factor its fixed degree over L, take a root zeta^(uk),
solve its finite-field DLP, and verify the six candidate scalars. In the original
computation z was already available, so this extra polynomial cannot improve the
ordinary pairing reduction merely by hiding z and then recovering it. Only the
known order-six ambiguity is removed.

Pay field/H construction and certification, pairing evaluations, the fixed number
of O(logq) extension-field exponentiations, coefficient arithmetic/storage,
factorization if needed and finite-field DLP. Seven coefficients already occupy
extension-field storage. No extension-degree lower bound is inferred, and
small-embedding-degree pairing advantages are prior art, not a new readout.
This does not evaluate chi_q(1+k^6) before exponent recovery.

## Exact falsifier of the proposed norm/trace descent

Take the polynomial norm, meaning PRODUCT OF FROBENIUS-CONJUGATE POLYNOMIALS
(not applying a field norm separately to each coefficient):

`N_Q(T)=product_(0≤j<r) P_Q^(p^j)(T)`.

Put V=<U,p> in Fq* and d=|U intersect <p>|=gcd(6,r). Each element of V occurs
exactly d times among up^j, since the product map U×<p>→V has kernel of size d.
Therefore

`N_Q(T)=(product_(v in V)(T−zeta^(kv)))^d`.

This identifies k only modulo V, a potentially larger ambiguity. If V=Fq* and
k≠0, N_Q(T)=Phi_q(T)^d independently of k. In particular r=q−1 gives d=6.
Likewise

`Tr_(L/Fp)(sum_(u in U) zeta^(uk))=d*sum_(v in V) zeta^(kv)`,

which equals −d when V=Fq*. The multiplier d is interpreted in Fp. These are
exact conditional identities, not a claim that all curves have such embedding
degree or that every descent loses information. When V is smaller, retained
information still needs paid construction and decoding. No numerical screen is
justified for the stated universal norm/trace readout.

## What the cited genus-character theorem actually accepts

Sol read the 2020 accepted CSV manuscript §§2.3–2.5, §3/Theorem8,§3.1:
https://biblio.ugent.be/publication/8665556/file/8665557.pdf
and the 2022 extended version, corresponding sections plus §5.1 and§6:
https://biblio.ugent.be/publication/01GP3YFJ87KV2ZKET1X9NH5PJ8/file/01GP3YGS40G691RWW1F0CSP7R1.pdf
The ePrint fetch returned403; author/institution manuscripts were read instead.

The elliptic interface compares curves in the same ideal-class orbit with common
endomorphism order O and Frobenius orientation. Its assigned odd-prime character
requires m dividing Delta_O=f²Delta_K; m may divide the conductor. The character
is the quadratic symbol of an appropriate ideal norm modulo m. Extensions and
volcano-floor descent are allowed, so the raw demand mu_m⊂Fp was too restrictive.

More decisively, substituting m=q fails this literal elliptic theorem. With
t=p+1−q, t²−4p=(p−1)² modq. Since Delta_O divides t²−4p and q∤p−1, q∤Delta_O.
This applicability calculation is not a lower bound for other constructions.

The extended paper's §5.1 charges extension degree kappa≤m−1, pairing work
O(log m*M_(p^kappa)) and worst-case volcano descent
O(h*m^(3+epsilon)*log p*M_p) under its fast-arithmetic assumptions. Compatible
torsion, field/order data, storage and pairing-output logarithms remain paid.

Its §6.1 conditional ppav construction detects a polarized isogeny multiplier
character under coprime degree and NONTRIVIAL CYCLIC rational m-primary torsion.
It is not a complete surface genus theory and does not identify its output with
chi_q(1+k²) or the symmetrized character.

For our q²-isogenous A_Q~E², #A_Q(Fp)=q². Frobenius satisfies the same elliptic
quadratic relation, whose distinct roots modq are1,p, each with multiplicity2
on A_Q[q]. Rational q-torsion therefore has rank2, not cyclic; over extensions
it has rank2 or rank4 when p^kappa=1 modq. Thus the literal m=q §6.1 interface
also fails. The quadratic relation, not only the repeated characteristic
polynomial, ensures the semisimplicity used here. No noncyclic pairing method
or other surface invariant is excluded by this observation.

## Research disposition

The explicit repair gives ordinary pairing recovery; its proposed norm/trace
descent has the stated exact loss of distinctions. The cited source does not
supply an alternative extractor under the proposed hypotheses. A useful new
bridge still needs a paid public representation, scalar-sensitive readout and
recovery advantage. Symmetrizing a polynomial in unknown k supplies none of
those operations. Verified complete-work gain NONE; ordinary square-root
reference unchanged. Grok/Fable independent initial proposals remain live.
