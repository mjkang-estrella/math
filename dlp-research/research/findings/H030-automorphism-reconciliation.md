# H030 quotient-line maps: valid constructions, rejection not established

2026-10-08. Claude Opus initial report/task handle in H030-automorphism-opus-raw.md;
native Astra separately checked algebra, scope and primary slides. Root checked
the identities and logical implications. No numerical run, multiplier-order
calculation, implementation or Lean claim. Verified improvement NONE.

## Accepted explicit operations

On E:y²=x³+b, p>3 with rational cube-root automorphisms, u=x³ identifies order-six
orbits of nonidentity points in a prime-order subgroup q>3. The maps are

    u_s=-(u+4b)^3/(27u²),
    u_2=u*(u-8b)^3/(64*(u+b)^3).

The former corresponds to a consistently chosen sqrt(-3) endomorphism/eigenvalue;
the latter to doubling. The raw y formula satisfies the curve equation; its sign
must match label bookkeeping or be included in the unit ambiguity at recovery.
Nonidentity denominators cannot vanish: x=0 implies3-torsion, y=0 implies2-torsion.
O still needs explicit dispatch. Literal evaluation is6M+S+(I-3M)/n using the
stated small-constant/addition convention. This is not a minimum over circuits.

For an orbit collision between multiplier-labelled starts, try the six unit
ambiguities, solve the corresponding nonzero-coefficient scalar equation and
verify on the original curve. All label work, starts, reporting, failures and
verification remain paid. One-coordinate states and absent canonicalization
are potential mechanisms, not a proved useful-collision advantage.

If a nonidentity q-torsion point returns to its unit orbit after multiplier
product M, M-zeta kills that point. For M-zeta nonzero,

    q<=deg(M-zeta)=N(M-zeta)<=(sqrt(N(M))+1)^2.

This valid short-cycle bound does not imply rapid exploration or useful hits.
Literal larger-orbit enumeration pays for all orbit members; its cost screen
does not reject an unconstructed cheaper invariant or alternate detector.

## Rejected overclaims

Indegree moments of independently selected permutation maps do not establish
an exact collision-time penalty1/sqrt(1-sum p_i²). Hence the report's7.6-unit
threshold, minimum number of cheap multipliers and optimized norm7 rejection
are not decisive falsifiers. Deriving another formula does not fix the missing
trajectory law. No numerical multiplier-order check is currently admitted.

[Bos–Costello–Miele primary slides](https://www.iacr.org/workshops/pkc2014/slides/4-2-EC-HEC-security-analysis.pdf)
report a particular BN254 implementation's arithmetic assumptions and measured
speedup0.790sqrt6. Historical normalization is not an optimal baseline, universal
27% improvement ceiling, or current hardware calibration. The competent
comparator must already receive known order-six and cycle-handling benefits.

The descent lemma also needs scope. For nonzero endomorphism alpha commuting
with the units, a rational-map identity

    pi(alpha*zeta*P+T)=pi(alpha*P+T)

forces one unit branch generically; surjectivity gives that branch=zeta and
T=zeta*T. A primitive sixth-root unit forces T=O. This does NOT cover alpha=0,
endomorphisms vanishing on a chosen finite subgroup, piecewise rules,
correspondences or symmetrized invariants. 'At most6 automorphisms' concerns
origin-preserving geometric automorphisms in characteristic>3, not translations.
Therefore it does not classify every canonicalization-free search operation.

## Decision

Retain the quotient maps and scoped norm/descent results. No supported complete
gain and no universal rejection. Missing premise: a paid useful-collision and
detection law for the actual multiplier walk against a matched order-six baseline.
Current numerical priority remains the more concrete C1 arithmetic review;
no experiment follows merely from this raw report's attempted rejection.
