# Source039: prefreeze calculations

No frozen statement and no nominee. Exactly one family, Source039 with its companions. Working question: for every r>=10, every d>=0 and m>=1, and a very general ordered tuple of r distinct complex plane points, does the homogeneous system have h0=max(0, binom(d+2,2)-r binom(m+1,2))? This is the classical homogeneous SHGH question, not a new conjecture, not a replacement for W136/I142/relative symplectic packing, and not a claim of current worldwide open status.

## First strongest composition

Write D=dH-mE and N=sqrt(r)H-E on the blowup. Source039 supplies N strictly nef, N^2=0, for all r>=10. It excludes h0(D)>0 when d<=m sqrt(r). If d+3>(m+1)sqrt(r), A=D-K=(m+1)N+[d+3-(m+1)sqrt(r)]H intersects every curve positively and has positive square. Nakai gives ampleness for the integral class A; Kodaira vanishing (or nef-big vanishing) gives H1(D)=0. H2(D)=0 for d>=0 by its negative H-degree dual. Hence only the finite-width, infinitely long strip

    m sqrt(r) < d <= (m+1)sqrt(r)-3

remains after this basic composition. Ciliberto–Miranda2011 Proposition2.3 already gives this asymptotic Nagata/vanishing mechanism. It is paid, not a new contribution. Their Theorem0.1 also covers d/m>=174/55 for r=10, with genuine throwing/transversality operations whose proof is being read. Those operations must not be discarded because a limiting theta matrix has a deficient example.

## Actual source proof has a stronger finite interface

All six substantive plane source sections have been read. The source polynomial space W after nine zero normal displacements has exactly

    dim W = binom(d+2,2)-9 binom(m+1,2),

for d>3m. Its q=r-9 collided-point rows number q*m*(m+1)/2. Thus the dimension difference equals exactly the expected Euler characteristic, with no leading-order error. The source proves injectivity below the Nagata slope by polygon contraction and taking powers. The normal-polynomial and theta identities themselves apply at d>3m; the below-slope assumption is used for contraction, not for their algebraic dimensions.

For nonsquare r, put a=3(sqrt(r)-3), h=3(d-3m), u=floor(d/3), choose rational 0<Delta<1/2 and xi as in source02. For j<=m, U_j=(d-3j)(sqrt(r)-3)-h*Delta/9 and n_j=h. For j>m, U_j=(d-3j)(sqrt(r)-3)-n_j*Delta/9, n_j=3(d-3j). Include integer (j,K) with U_j<K<U_j+n_j, plus (d/3,0) when 3|d. The finite matrix is B[(ell,b),(j,K)]=K^ell*j^b, b<m, ell<q(m-b). Its entries and floor choices are exactly reproducible using rational arithmetic and square comparisons, without floating-point decisions.

The original necessary-polynomial statement preserves existence. For a dimension claim one must pay a filtered-kernel/Grassmannian refinement, not silently promote it. The natural approach is the finite G_B-adic filtration and its Rees lattice. At the nine zero-displacement points, positive-degree elliptic restriction bundles (d>3m) allow successive H1 vanishing and give gr(V9)=W. Normal-rescaling the remaining q points then bounds the generic kernel dimension by the limiting kernel. A complete dimension-transfer formulation is still to be written only if it helps close a full target.

Initial exact finite modular minors witness maximal rank for (r,d,m)=(10,19,6),(10,38,12),(10,57,18),(10,22,7),(11,10,3),(12,7,2),(14,15,4),(15,4,1). A modular deficiency at (13,11,3) is only a prompt for exact analysis, not proof of rational rank deficiency or failure of the geometric system. These tiny cases have low multiplicities or occur in classical ranges and are not nominees. They are diagnostic tests of the actual source interface.

No full all-r,m finite rank mechanism has been proved. The source's contraction loses precisely the finite additive boundary information; powering preserves slope but does not infer original H1 from large-multiple H1. Other compatible theta charts, uncollided points, general diagonal reductions, birational throws and finite minor lifting remain available and must be tested before calling a residual unpaid.
