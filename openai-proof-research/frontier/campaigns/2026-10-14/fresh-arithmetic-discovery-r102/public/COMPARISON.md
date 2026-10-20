# Strongest-reduction comparison and nomination limits

This is the author's comparison, not a contribution verdict. The nominee is the
entire frozen T009P102, not a renamed noninjective Hom theorem or a restricted
piece of r97/r98. One family, 009, supplies the mathematical base. The broad
catalogue screen did not produce a claimed absence or priority certificate.
The family has prior project work; the higher-coefficient operation was less
developed, rather than the whole family being untouched.

## What is already paid

1. **Pinned equal-characteristic reconstruction.** `thm:main` gives the full
   n=1 classification with scalar and field-map uniqueness. Its actual proof
   supplies p-bases, logarithmic determinant tests, the intersection/exponent
   calculation, global scalar propagation and projective lifting. These are
   accepted as operative. No claim is made that its affine construction fails
   at its stated input. Its once-recovered field map can be used at all higher
   levels without repeating line recovery.
2. **The coefficient filtration.** Frobenius injectivity and the classical
   no-p-torsion theorem for K_2 identify the last layer with mod-p data.
   Subtracting identity and expanding a product gives the linearized Steinberg
   equation. r97's actual work/notes.md, final two lines, already anticipated
   this reduction and named the infinitesimal rigidity problem. That idea is
   credited, not presented as newly found in r102.
3. **Jacobson.** The identity D^(p-1)(D(u)/u)+(D(u)/u)^p=D(u)/u for D^p=D,
   including its necessity for a logarithmic derivative, is classical. The
   two-logarithm scalar comparison in Lemma 2.2 is an immediate consequence.
   Equations (28)--(33) and Theorem 15 of the actual 1937 proof were read.
4. **After rigidity.** Induction over n, scalar normalization, named-base
   compatibility and uniqueness of the coefficient unit are routine. They
   are written out for correctness, not offered as the new operation.

## The precise proposed additional operation

The unresolved statement in the operative r97 notes was a classification of
*all* F_p-linear endomorphisms delta satisfying the linearized Steinberg
relations. Proposition I supplies that classification for every field of
finite p-rank at least two. No finite-rank, injective, surjective or geometric
condition is imposed on delta.

Its proposed contribution is the conversion of the mixed linearized relation
into two genuine logarithmic derivatives along each transverse Euler
coordinate, with ratio f/(f+1). That ratio is killed by the transverse
coordinate derivation but is not Frobenius-fixed. Jacobson then eliminates
the transverse coordinate. Multiplicativity of eta propagates the resulting
scalar, and the p-basis intersections force it into F_p. This is the exact
operation on which any substantial-contribution case rests. It is not the
classical p-curvature identity, the n=1 field recovery, or changing the
coefficient parameter in a theorem statement.

The operation is short. A reviewer may judge this combination technical.
The author has no separate contribution gate and does not certify that it
meets the campaign's substantial threshold. The packet submits a full proof
and exposes this strongest reduction so that the parent can decide whether
to request independent correctness and contribution reviews. There is no
request to revisit a previously assigned TECHNICAL verdict: no such verdict
was assigned to this claim in the read operative history.

## Closest primary reconstruction proof

Cadoret--Pirutka, author version resubmitted 2019-08-28, Theorem 4 and
Corollary 10, reconstruct from multiplicative quotients by constants with
algebraic-dependence structure (or the corresponding integral Milnor
invariants). The actual proof in Sections 3.4--3.6 was read, including the
stronger descent from mod-p information back to the quotient by constants.
That descent does not merely stop at mod p: it controls the error using
formula (3.2), good pairs and exact multiplicative independence, then
varies auxiliary prime powers to obtain one integral exponent.

Those operations are fully credited. For the present input an arbitrary
compatible V_n-isomorphism is not supplied with a lift to F^times/k^times
or with all algebraic-dependence subfields. Applying the integral theorem
would require constructing that lift and its compatibility. The current
argument proves the coefficient-level rigidity directly. We do not use a
failed naive lifting attempt as evidence that the primary has no stronger
operation; the actual Section 3.6 is the comparison.

The pinned mod-ell companion's global-scalar proof (`08-compatibility.tex`,
`prop:global-scalar`) uses recognition of good rational subfields and true
divisors, continuity of order sums, and an exceptional divisor to align
scalars. The pro-ell companion's `local:commuting` and
`reconstruction:pop` operate with actual Kummer data at characteristic
unequal to ell and with all coefficient levels. Their input excludes the
equal-characteristic prime in T009P102. A lift from a single characteristic-p
coefficient level to those inputs is neither supplied nor asserted. No
companion theorem is weakened to manufacture an apparent gap.

## Operative history

- r24's complete screen-009.md: injective transfer is source-paid; noninjective
  maps include valuation and inseparable field examples. No full theorem was
  frozen. That old scope is not changed.
- r97's complete report and work notes: characteristic-two lineation reduction,
  general valuation models, quadrangle lemma, base-free n=1 screen; the final
  work-note paragraph records the higher-p-power/infinitesimal route without
  its proof. This is the direct research antecedent.
- r98's complete report: Machala plus source multiplicativity gluing closes
  its noncollapsing characteristic-two stratum as an author technical screen;
  collapsing and odd-characteristic Hom classification remain unresolved.
  T009P102 makes no claim about those unresolved Hom scopes.
- r101 parent assessment/intake and r99 disposition were read as required.
  Their DEG/prime-thinning/FS-FP operations do not occur in this proof. Their
  statuses and original scopes remain untouched. No r101 desired-grade
  rereview is requested. r100's provider failure is irrelevant to the proof.

No mechanism overlap with the original T047S74, T271D110, T085E111,
T191V56, arithmetic r69, T238B125, T096N126 or T195D93 was identified in
this selected argument. Their full mathematical archives were not consumed
or weakened. This is a disclosed scope limit, not a global history clearance.

## Why mod-p reduction alone is insufficient

Let F=k(s,t) with k algebraically closed of characteristic p, and v_s the
s-adic valuation. The formula

    Psi([f]_2)=[f]_2+p v_s(f)[t]_2

is a well-defined A_2-linear automorphism of V_2(F), with inverse given by
the minus sign; its extra operator has square zero since v_s(t)=0.
It reduces to identity modulo p. But it does not preserve Steinberg:

    {Psi(s),Psi(1-s)}=p {t,1-s} in K_2^M(F)/p^2.

The mod-p symbol on the right is nonzero because its differential symbol
is -(dt/t) wedge ds/(1-s), which is nonzero. By p-torsion-freeness its
p-multiple is nonzero modulo p^2. Thus an arbitrary lift cannot be assumed
compatible. This is an elementary explanatory example, not an additional
nominee or a priority claim.

## Literature and gate limits

The actual primary interfaces used are Jacobson's logarithmic derivative
identity and Geisser--Levine's no-p-torsion theorem; Cadoret--Pirutka is the
main reconstruction comparison. Izhboldin's author survey is corroborating
context, not a replacement for the read theorem/proof in Geisser--Levine.
Targeted web searches for Milnor-K derivations, infinitesimal rigidity and
finite prime-power reconstruction did not produce a directly matching
primary theorem in the inspected results. This is a bounded-search
observation, not a worldwide absence, originality or open-problem claim.
No correctness, contribution, acceptance, priority or count is self-awarded.
