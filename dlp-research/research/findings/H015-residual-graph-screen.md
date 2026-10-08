# H015 residual quadratics: valid relation bridge, no cheaper dependency selector

2026-10-08. Native Astra independent proposer and correction followup; root
checked the divisor/graph algebra and added the known-anchor comparator.
No experiment, new Lean theorem or validated improvement. The previous H014
feature result is not used to reject this unrelated mechanism.

## Executable relation construction

Choose affine-labelled P_i=a_iG+b_iQ with distinct abscissae. Let ell(X) be their
chord polynomial and, for t!=0, set

    F_t(X)=ell(X)+t*(X-x1)*(X-x2).

Divide F_t(X)^2-(X^3+A*X+C) by(X-x1)(X-x2). The quotient is quadratic. Test its
discriminant, extract roots when they exist, reconstruct points U,V on y=F_t(x),
and verify membership/multiplicities. Nonsplitting and degenerate cases are paid.
The pole divisor of y-F_t(x) is4O, so its zeros give

    P1+P2+U+V=O,
    z_U+z_V=-(a1+a2)-(b1+b2)*k modq.

This is a real affine constraint without individual known logarithms for U,V.
It bypasses H013's globally rational single-branch label obstruction by retaining
both unknowns. It does not assume a factor-base decomposition or large root oracle.
Constant polynomial degree is NOT zero field cost: interpolation, division,
discriminant testing, square roots, reconstruction and verification are charged.

## Exact sparse elimination and known anchors

Keep a vertex per point, with signed affine potentials
z_v=epsilon_v*z_root+alpha_v+beta_v*k, epsilon in{+1,-1}. An edge
z_u+z_v=c+d*k in one component yields

    (epsilon_u+epsilon_v)*z_root
      +(beta_u+beta_v-d)*k = c-alpha_u-alpha_v.

If the root coefficient is0 and the k coefficient is nonzero, recover k and
verify. Coefficient +/-2 instead expresses the root affinely in k (q odd).
An independent closing constraint on that anchored component can then recover k;
an ordinary new tree edge merely propagates a label. Register ALL labelled
inputs as anchors, exploit residual-to-anchor hits and paths between anchored
components, and retain coefficient-zero failures. Graph rank is not free.

## Correcting the initial cost screen

The initial proposal's linear-q cycle threshold applies only to an UNANCHORED
independent uniform-endpoint graph on Theta(q) vertices. A repeated vertex near
birthday scale normally just merges two trees, rather than supplying a cycle.
But actual inputs already have affine labels and cannot be ignored as anchors.

With M emitted edges and A=Theta(M) distinct known-labelled anchors, a separate
ideal independent model predicts O(M*A^2/q^2)=O(M^3/q^2) direct anchor-to-anchor
edges. Its candidate-event threshold is q^(2/3), not q. A nonzero scalar-recovery
coefficient remains an additional condition. Paths of length ell have scale
O((A^2/q)*(C*M/q)^ell); for M=o(q), longer paths are suppressed in that model.
These are explicitly CONDITIONAL random-edge comparisons, not a bound on
adaptive geometric endpoint selection or an optimal ECDLP exponent.

Fresh random labelled inputs already have ordinary useful birthday collisions
around sqrt(q). A competent implementation/baseline must detect and credit
them. Collecting many anchors cannot erase that cheaper available solver.
Root identified this qualification; proposer independently confirmed and withdrew
the broader linear-q wording. No numerical graph run is needed for this model.

## Reusing one endpoint does not supply a new cheap primitive

For a chosen finite U with x_U distinct from x1,x2, forcing the parabola through
it gives

    t=(y_U-ell(x_U))/((x_U-x1)*(x_U-x2)),
    V=-P1-P2-U.

The other residual is already computable by ordinary group operations. t0 is a
degree-drop case and is outside the quartic card; its fourth intersection is O.
For fixed C=-P1-P2, U->C-U is an involution: a matching plus its unique fixed
point 2U=C. Repeating such edges is tautological. Varying known-labelled C gives
affine group transitions, not a cheaper residual-root algorithm. If U has no
known affine label, its initial logarithm stays as an extra unknown.

## Disposition

Sparse relation-graph elimination is established methodology. The relevant
prior-art lead is [Gaudry--Thome--Theriault--Diem](https://eprint.iacr.org/2004/153),
whose hyperelliptic double-large-prime result is not automatically an elliptic
algorithm. No novelty or complexity guarantee is attributed here.

Park pending an explicit cheap selector producing INFORMATIVE closing constraints
earlier than the applicable input-collision baseline. Required full gate:
C_setup+N*C_trial+C_graph+C_verification<W_matched_baseline, including failed
roots, target/input generation, anchor lookups, coefficient-zero closures,
memory and all available ordinary collisions. No selector meeting that gate was
supplied. The conditional random-edge model and forced-endpoint comparator reject
the stated justifications, not all coordinate-aware graph constructions.
