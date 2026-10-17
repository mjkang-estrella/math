# A parity boundary and a different survival test

Myeongjin Kang; no affiliation. CC BY 4.0 prose; MIT code.
Research deductions for G4; no independent proof gate or acceptance claimed.

## Exact comparison and product hypotheses

The scheme input is Weibel VI Theorem4.2 for smooth schemes over a field,
with coefficients Z/5, and Addendum4.2.1: 5 is not 2 modulo4, so the
coefficient spectral sequence is multiplicative; the integral/coefficient
module pairing is also compatible. Characteristic zero ensures that 5
is invertible on each curve under consideration. We use the corrected
construction described in VI.4.4, not the historical incomplete construction.
Finite-type smooth affine opens give the spectral sequences first; the
localizations T and T0 are then handled by filtered continuity. Their
relevant diagonals have finitely many possible entries, so the finite
filtrations and maps commute with this filtered colimit. No spectral
sequence for the mixed-characteristic total ring itself is assumed.

The product compared with H4 is specifically the composite

 K3(A) x K1(B0) -> K4(B0) -> K4(T0;Z/5),
 (c,[z]) -> reduction(restriction(c*[z])).

Integral generic vanishing was proved by the source for c, hence holds
for this product before any coefficient comparison. Nonvanishing in H4
would detect its integral preimage, but vanishing in H4 would only show
that this particular mod-five detector fails; it would not prove that
the integral class is zero.

## The original p-adic model has no degree-four detector after inverting pi

Let A and L be the exact degree-three source model, T=Spec A[1/pi],
and F=Frac A. Then the following supporting statement follows from the
standard scheme motivic spectral sequence:

    K4(T;Z/5) -> K4(F;Z/5) is injective.

Here is the argument, including why the dimension and coefficient hypotheses
matter. A is regular local, hence factorial. A[1/pi] is a regular factorial
ring of dimension one, so Pic(T)=0. The regular locus of the generic curve
C is smooth over the characteristic-zero field L. Its complement misses T.
Thus T is a filtered inverse limit of smooth affine opens of C. All
K-theory, motivic, and finite etale cohomology groups below commute with
this system of localizations.

A smooth affine curve over an algebraic closure has etale cohomology with
constant Z/5 coefficients only in degrees 0 and 1 (Stacks, 03RN,
Lemma 59.69.3). The same holds with the constant Tate twists. Since
cd_5(L)=2, Hochschild--Serre gives H^s(T,mu5^j)=0 for s>3.

In the motivic spectral sequence, write s for cohomological degree and j
for weight, so the K-degree is 2j-s. For a smooth curve motivic groups
vanish for s>j+1; for s<=j they are the etale groups. The remaining
s=j+1 group injects into etale cohomology, by comparison of the motivic
and etale localization sequences. These statements are the operations
in Weibel VI.4.1--4.2 and Example 4.6 (the localization argument works
for affine opens as well as the displayed projective curve).

On the total-degree-four diagonal the only possibly nonzero groups are

  (s,j)=(0,2): H^0(T,mu5^2),
  (s,j)=(2,3): H^2(T,mu5^3).

The other possible curve terms are (4,4) and (6,5), both zero by the
cohomological bound and the just stated comparison. Larger weights
vanish by s>j+1, and negative s groups vanish.
A differential d_r changes (s,j) to (s+2r-1,j+r-1). Neither displayed
term has an incoming differential. Outgoing differentials from H^2
have degree >=5 and vanish. The only possible differential from H^0
is d_2 to H^3(T,mu5^3); it is zero because this H^0 line is represented
by beta^2, a genuine K4 coefficient class pulled back from L. Its
nonzero edge follows from the source's nonzero Bott edge and the
coefficient product of the degree-five companion. Thus there is a
natural filtration

  0 -> H^2(T,mu5^3) -> K4(T;Z/5) -> H^0(T,mu5^2) -> 0.

The same filtration holds for F (cd_5(F)<=3); its H^0 line likewise
survives by beta^2. H^0 restriction is injective. As zeta trivializes
the Tate twists, H^2(T,mu5^3) is identified with H^2(T,mu5). The Kummer
sequence and Pic(T)=0 identify this with Br(T)[5]. Brauer restriction
Br(T)->Br(F) is injective for regular integral schemes (Colliot-Thelene--
Skorobogatov, 31 October 2019 author book, Theorem 3.5.4, proof read).
Hence restriction on both graded pieces is injective. A diagram chase
proves the supporting statement.

Consequently every integral x in ker(K4(A)->K4(F)) has ZERO reduction
modulo five after restriction to T. This does not prove x=0 in K4(A).
It rules out a particular detector, not G4. It also does not apply to
B0: its generic coefficient field is L(z), of cohomological dimension
three, so the affine-curve bound is four, not three.

## A new precise cohomological test for the suspended candidate

Put T0=Spec B0[1/pi]. It is a factorial localization of a smooth curve
over L(z). The same spectral-sequence calculation now permits the extra
term H^4(T0,mu5^4). It has no outgoing differential. The only possible
incoming differential is d_2 from H^1(T0,mu5^3). Since Pic(T0)=0,
Kummer says that every class in this H^1 group is a unit Kummer class
with a constant twist. It is represented in K5 by beta^2 times that
unit. Thus it is permanent, and d_2 is zero. There are no other incoming
terms, since their cohomological degrees would be negative. Therefore
H^4(T0,mu5^4) is the top weight subspace of K4(T0;Z/5).

For the source c, its coefficient reduction on T is nonzero and generically
zero. On degree three the two possible terms are H^1(T,mu5^2) and
H^3(T,mu5^3). Restriction on H^1 is injective (a finite etale torsor
trivial at the generic point of a normal integral scheme is trivial).
The possible incoming differential to H^3 vanishes by permanence of
beta^2. Thus c determines a nonzero class

  alpha in H^3(T,mu5^3).

Multiplicativity identifies the reduction of c*[z] on T0, in its top
weight subspace, with

  res(alpha) cup (z) in H^4(T0,mu5^4).

This supplies a different exact nonvanishing problem. A proof that this
cup product is nonzero would establish survival of the already integral,
already generically zero c*[z], and therefore solve full G4 using B0.
But NO such nonvanishing proof is obtained here. The localization from
T times G_m to T0 is essential; the old Bass residue and ordinary
Laurent-series map do not survive it. The reconstructed moving divisor
also prevents claiming that proper pushforward followed by the two
valuation boundaries detects this cup product. The cohomological test
is a research reduction, not a replacement target or a theorem nomination.

## Other route checked

One might complete A in its maximal ideal and use a completed Laurent
ring allowing infinitely many negative powers whose coefficients tend
to zero. Such a ring can invert z+a by its convergent geometric series,
so the parent's ordinary-Laurent obstruction does not automatically
apply. However one would need to prove survival of the source c under
completion and in the appropriate continuous K-theory, then construct
and compare a residue there. Neither source theorem supplies those
premises. We do not assert them or confuse continuity in filtered
localizations with continuity in inverse limits of infinitesimal thickenings.
