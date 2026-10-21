# Concrete cylinder tests and prefreeze decision

These computations test attempted NEW applications. They do not audit the stipulated source or challenge any prior immutable full target.

## 1. A specified retraction need not give a single positive right cylinder

Take the four-element diamond poset E with a<b<x and a<y<x, b and y incomparable. Let A={a,b}, a sieve, and r(a)=a,r(b)=b,r(y)=a,r(x)=b. It is the right-adjoint retraction, since r(z) is the greatest old element below z. Set f=ir, g=id_E. They agree on A and f<=g, but g is NOT constant on E\A, so source relative-prism does not apply.

Test a right Gray cylinder with these endpoints, stationary on U(A), in dimension2. Its vertex components are forced: at y the only path r(y)=a -> y is [a,y], and at x the only path b -> x is [b,x]. On the edge [y,x], the right tensor differential would require a positive two-chain h satisfying

  d h = [b,x]-[a,y]-[y,x]+[a,b].                            (1)

There are only two positive two-simplex generators in E,

  t0=[a,b,x],   d t0=[b,x]-[a,x]+[a,b],
  t1=[a,y,x],   d t1=[y,x]-[a,x]+[a,y].

Equation(1) forces h=t0-t1 by comparing [b,x] and [y,x] coefficients. No nonnegative combination works. Equivalently, the required naturality square would compare the two incomparable paths S={a,y,x} and S'={a,b,x}; Ara--Maltsiniotis10.4--10.5 permits a 2-cell only when the source chain is a subset of the target chain. Neither inclusion holds. Reflection to2 does not change 1-cells, and no 3-simplex is available in this poset to change the calculation. Thus this particular SINGLE right-cylinder construction fails.

This does not obstruct a zigzag. The SOURCE supplies it explicitly. Define k to fix A and send y,x to b; define q to fix A and send y,x to x. Then

  id_E <= q,     k <= q,     ir <= k,

with upper maps q,q,k respectively constant on the complement. Each comparison satisfies source relative-prism. After every attachment it gives the stationary strict-cylinder zigzag

  id_Y -> Q <- K <- (j p_r),                               (2)

where p_r is the retraction induced by r. In particular the naive failure in (1) is paid by the stronger source operation; it is not a finding or a counterexample to a relative homotopy claim. For general E the fixed-vertex descent in note02 replaces a global choice of q. It assembles the weak-equivalence conclusion without purporting to assemble one strict Gray cylinder.

## 2. A primary NERVE homotopy is not automatically stationary as a Gray cylinder

Gagna6.6--6.8 uses the positive concatenation formula

  H(phi,z)[j0,...,jm]
       = f(z)[j0,...,jk] g(z)[j(k+1),...,jm]

at the cut of phi. It gives a simplicial homotopy, including the unit deformation in6.9. Even setting f=g=id does not make this formula pointwise the constant homotopy on every higher simplex.

Here is an explicit test in U_3([3]). Let z:O_2->U_3([3]) have vertices0,2,3, edge01 represented by [0,1]+[1,2], edge12 by [2,3], edge02 by [0,3], and its top2-chain

  z[0,1,2]=[0,1,2]+[0,2,3].                               (3)

Its boundary is [0,1]+[1,2]+[2,3]-[0,3], as required. The entries define a positive augmentation-preserving chain map, so Steiner's table construction gives the stated strict functor. At the cut phi=(0,0,1), with f=g=id, the formula instead gives

  ([0,1]+[1,2])[3]=[0,1,3]+[1,2,3].                       (4)

These are distinct positive two-chains and distinct2-cells in U_3([3]); 3-dimensional reflection does not identify2-cells. Their difference is d[0,1,2,3], which is a higher comparison, not equality at dimension2 in U_3. Thus this natural primary nerve homotopy cannot simply be glued to a CONSTANT old-side Gray cylinder on arbitrary U(A). The source's whole-map stationarity factorization is stronger and was explicitly checked in its proof.

This is a diagnostic of that formula, not an assertion that no suitable relative homotopy exists. The identity itself of course has a constant cylinder. It also does not contradict Gagna, whose construction claims the nerve homotopy, not the invalid strict stationarity inference. Dimension2 truncation would identify (3) and(4), so this diagnostic must retain n>=3.

## 3. Decision

The full arbitrary-action fixed-nerve comparison and the actual categorical (BC) WEAK EQUIVALENCE have closed in note02. The compatible orbit-diagram and dimension-change constructions in note03 show why stopping at a proposed equivariant model structure or a collection of Quillen equivalences would miss the strongest existing payment. The mechanism is identifiable and fully carried out: primary target-path support; source stationary relative prisms; fixed terminal-vertex sieve diagram; explicit contractible simplex fibers; source cosieve reattachment; and canonical comparison triangles.

Those operations are a composition of the stipulated source's hard proof machinery and read classical/primary constructions. The expanded action scope alone is not being offered as a substantial result. No correctness or contribution verdict is assigned to it here.

The exact further algebraic operation left unpaid is strict, all-dimensional fixed-class REPRESENTATIVE AND EQUALITY descent for the mixed attached cells, at the full quantifiers of note01(BC). The concrete mixed presentation and failed rewrite in note03 specify what would have to be added to upgrade the canonical weak equivalence to an isomorphism. The cylinder calculations explain why a naive single-cylinder or nonstationary-primary-homotopy shortcut does not supply that operation, while preserving the source's stronger zigzag payment. This strict operation is an exploratory direction, NOT a frozen target, NOT claimed necessary for every substantial next result, and NOT claimed false or impossible.

PREFREEZE / no nominee. No weaker or renamed old target, no author-proof nomination, no acceptance/count change, no downstream work. All supplied prior full scopes and dispositions remain unchanged, including S176A's unresolved correctness condition. This is not exhaustion or a global priority/impossibility statement.
