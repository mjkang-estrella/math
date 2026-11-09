# Diagnostic locality regression (ordinary proof)

Use the reviewer's precise pair
p*(Z,W) = p6(Z,-W)(2+Z-W),
q*(Z,W) = q6(Z,-W)(2ZW+W-Z).
The accompanying exact Python check verifies reduction and reflection in bidegree
(4,3), the root formula, and the height limit. Stability follows from that of
p6 and |Z-W| < 2 in the open bidisk. This is a reduced rational inner pair.

At Z = -1 the first numerator factor is -8i(W+1)^2. It is nonzero
on the compact closed ball |W-1| ≤ 1/2. By continuity, uniformly on this
compact ball it remains nonzero for Z sufficiently close to -1. Thus every
zero in this ball comes from the linear factor, whose unique root is
v(Z) = Z/(2Z+1). This root tends to 1. Consequently it belongs to every
prescribed positive neighborhood of 1 for all sufficiently small |Z+1|.
For |Z| = 1 and h = |Z+1| > 0,

1 - |v(Z)| = 1 - 1/sqrt(1+2h²)
            = 2h²/[sqrt(1+2h²)(sqrt(1+2h²)+1)].

For h < 1 this lies between h²/3 and h²: the denominator is at least 2
and at most sqrt(3)(sqrt(3)+1) < 6. The root lies in the disk for h > 0.
Take rho0 = 1/2, c = 1/3, C = 1, and shrink delta0 to enforce the
uniform separation and h < 1. The displayed estimates prove the repaired
predicate with K = 2. Its upper clause holds for every rho in (0,rho0]
by v(Z) → 1, preserving C = 1. No other zero lies in the lower neighborhood.

It cannot satisfy the repaired predicate with K = 6. If it did, choose its
upper neighborhood inside the separation ball. Its witnesses would necessarily
be v(Z), so h²/3 ≤ C h⁶ for all sufficiently small positive h, impossible.
Equivalently apply the general uniqueness argument proved in Lean. This
particular pair's contact-two construction and separation are ordinary proofs,
not Lean declarations. The Python calculation verifies exact algebra and a
limit, not the compactness or all-neighborhood quantifiers.

The old predicate can use radius 3 to borrow the sixth-order cluster at -1,
or a small radius for order 2 at 1, as established by the preserved review.
No assertion that this diagnostic product is a graph resolvent is needed.
