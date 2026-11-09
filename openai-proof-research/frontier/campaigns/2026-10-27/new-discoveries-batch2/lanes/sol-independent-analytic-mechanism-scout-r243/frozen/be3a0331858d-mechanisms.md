# Sustained mechanisms and rejected shortcuts

The cube route uses two different constructions and an independent invariant proof, as detailed in PROOF.md. The exhaustive dimension4 route was negative; no assertion about all dimensions followed from it. The cycle route models X with gX differing in exactly two points: take unions of full g-cycles and one proper consecutive segment in one nontrivial cycle. Its union Z is then searched for a metric asymmetry between the two deleted endpoints. This is a structural search space, rather than arbitrary subsets of the5-cube. A24-point witness was reduced to six by complete enumeration within that one symmetry's cycle space. No minimality over all dimension5 witnesses is claimed.

## Complete classical bridge for the Genius identities (uncredited)

Federbush2002.03814v1 pp1–2 defines D(x)=Σ_(j=1)^p d_j x^j, U(x)=Σ_(j=1)^p u_j x^j, u1=1, and requires [x^p]exp(D)=0. The unique F1=1,F2,…,Fp satisfy
[x^p]exp(D+yU)=[x^p]exp(yΣF_i x^i).

Here is an explicit general formal-coordinate bridge, over a characteristic-zero coefficient ring. Write exp(D)=Σa_j x^j, so a0=1 and a_p=0. Set

A(x)=Σ_(j≥0,j≠p) p a_j/(p−j) x^j, z=x A(x)^(−1/p).

Fractional powers are uniquely defined formal series with constant term1. Differentiating gives
d(z^(−p))/dx=−p x^(−p−1)exp(D(x)),
because the missing j=p term is zero by hypothesis. Therefore
z^(−p−1) dz = x^(−p−1)exp(D(x)) dx.

The substitution has leading coefficient1 and a unique formal inverse h(z). Formal residue substitution, applied coefficientwise in y, now gives

[x^p]exp(D+yU)=Res_x exp(yU(x))exp(D(x)) dx/x^(p+1)
=Res_z exp(yU(h(z))) dz/z^(p+1)
=[z^p]exp(yU(h(z))).

Set F_i=[z^i]U(h(z)) for1≤i≤p. Terms beyond degree p do not affect the last coefficient. This proves the literal defining identity; the leading coefficient is F1=1. Uniqueness can also be verified directly: coefficient y^(p−i+1) determines F_i with nonzero multiplier1/(p−i)!, after F1,…,F_(i−1) are determined. Consequently these are exactly the source's F_i, rather than new surrogate functions.

Composition U↦U(h) is linear since h is independent of U. This proves Conjecture1 (affine in u2,… because u1 was fixed1). As a second route, formal Lagrange inversion gives the explicit finite formula

F_i=(1/i)[x^(i−1)] U'(x) A(x)^(i/p).

For fixed i and every integer p≥i, this uses only a_j with j<i. Those a_j are polynomials in d1,…,d_(i−1), independent of p, and p/(p−j) is a rational function regular at every p≥i. Expansion of the power to degree i−1 is finite, so F_i is a finite polynomial in u,d with coefficients rational in p. As p→∞, A's bounded-degree coefficients tend those of exp(D), while the exponent i/p tends0; hence A^(i/p) tends1 coefficientwise. It follows that F_i−u_i tends0 coefficientwise. This supplies exactly a finite monomial expansion with rational coefficients tending0, as in Conjecture2, for each fixed i. No uniform limit in i or random-graph consequence is asserted.

**Strongest classical objection, completed rather than waved away:** this is directly formal residue invariance plus Lagrange inversion after normalizing a Laurent differential. The sole resonant obstruction is its residue a_p, which the source explicitly sets to0. The two displayed identities give a complete ordinary classical-to-source bridge; no special new combinatorial mechanism is left. Therefore this lane does not nominate it for substantive discovery credit. `genius_check.py` compares the Lagrange formula against the defining polynomial identity using exact rational arithmetic for p2…9. Those checks support transcription only; the argument above proves the all-order statement. Historical/current arXiv query gaps remain, so no claim to first proof or worldwide novelty is made.

The later Federbush2012.10927v8 body was checked at its introduction, actual Theorems3.1/3.2 and AppendixB. It asserts bounded-parameter weak graph positivity, retains the all-parameter Awesome identity as a conjecture, and does not supply a general replacement for these two Genius identities. This bounded comparison is not an audit of its random-graph proof.
