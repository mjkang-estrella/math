# H021 adaptive relations: two constructions deduplicated

2026-10-08. Native Astra /root/h007_additive_relations initial pass completed;
root checked the displayed divisor/label identities against the accepted
H015-residual-graph-screen.md. No new surviving mechanism or numerical test.
This is paper algebra, not a Lean theorem or universal hardness bound.

For labelled P=aG+bQ, a nonzero f in L(dO) with divisor
(d-1)P+U-dO has U=-(d-1)P. Its residual label is already
(-(d-1)a,-(d-1)b). The stated divisor is an explicit condition: degeneracies,
lower pole order and multiplicities require handling. Jet interpolation and
residual extraction therefore do not add an independent scalar equation.
A faster evaluation of this fixed scalar multiple could still matter, but
needs a concrete arithmetic comparison; none was identified.

For an unresolved rational two-point divisor U+V, represent its distinct affine
abscissae by u(X) of degree2 and its ordinates by y=v(X) modulo u, deg(v)<2,
u divides v²-f_E. Set h_t=v+t*u with t!=0. The quotient
(h_t²-f_E)/u is quadratic. If it splits into verified points W,Z, the principal
divisor of y-h_t gives U+V+W+Z=O, with multiplicities/exceptions handled.
If the existing row says z_U+z_V=A+B*k, the residual row merely says
z_W+z_Z=-A-B*k. Changing t alone does not provide an independent recovery
equation. Splitting, roots, matching, coefficient checks and elimination cost
work. Useful new information requires an independent closing relation.

This is the existing H015 residual-graph operation at divisor level, not a new
selector or attack card. The identities do not exclude a future paid adaptive
choice that favors informative closures. The missing mechanism remains a
selector producing target-bearing independent dependencies more cheaply than
the ordinary collisions already available from labelled inputs.

No external new theorem or literature novelty claim is imported in this pass.
Do not inflate the candidate count with these restatements. Verified improvement
NONE; H021 representation and other H020 work continue independently.
