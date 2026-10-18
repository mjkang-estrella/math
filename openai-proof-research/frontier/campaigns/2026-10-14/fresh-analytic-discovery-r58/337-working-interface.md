# 337 equality screen — pre-freeze working derivation

This is author-side feasibility work, not a theorem claim or nomination. The contemplated full scope is every nonzero compactly supported integral n-cycle, n>=2, in every proper CAT(0) space whose least filling mass attains the sharp Euclidean coefficient. Expected conclusion: the cycle bounds a multiplicity-one isometrically embedded Euclidean ball. No dimension/subclass restriction is being substituted. Exact scope is not yet frozen: the endpoint and antecedents are under examination.

History: I286 develops dimension-only positive-deficit asymmetry stability for arbitrary finite-perimeter regions in smooth Cartan–Hadamard manifolds. That target remains unresolved and untouched. Its full report and disposition were read. I91 uses filling/variance only as a finite-configuration comparison. A search is not freshness clearance.

## Threshold operation for n>2

An equality cycle is a zero maximizer of V(B)-c_n M(B)^((n+1)/n), since the pinned sharp theorem already bounds this functional above by zero. Subadditivity gives the exact extremizer inequality used in source02. Scale M(A)=s_n. The source radial first-variation and small-set/Sobolev proofs appear to use only that inequality and c_n((n+1)/n) M(A)^(1/n)=1/n, not strict M(A)<s_n.

For Q(u)=4/(n-2) E(u)+n||u||_2², the constant test gives inf Q/||u||_p² <= S_*=n s_n^(2/n). If the infimum were strictly smaller, source05's concentration argument still constructs a subthreshold minimizer; source06–07 then contradict it. Thus the infimum equals S_*, and constant1 is an actual minimizer. Applying source06 with v=1 should give I(y)=integral d(y,x)² dmu(x)<=2s_n for mu-a.e. y. Source07 gives I(o)>=s_n and average I>=2I(o) at the barycenter. Therefore I(o)=s_n. Source radial inequality with center o and g=1 now saturates both Cauchy–Schwarz and sqrt(1-|Dr|²)<=1: r=1 mu-a.e. The cone filling has mass <=s_n/(n+1)=omega_(n+1), hence equals the minimum. To finish, apply the classical density-one rigidity below at its center, after checking the center belongs to support.

This is likely a technical threshold adaptation; it is not separately nominated. All endpoint dependencies still need a complete passage check.

## Classical volume rigidity already pays the final ball identification

Stadler, arXiv2212.07100v1, AppendixA.1 PropositionA.1 and full proof (extracted770–995 read), proves: if a compact area-minimizing integral k-current in a locally compact CAT(0) space has M(S restricted B(p,r))/r^k=omega_k at an interior-support point p with r no larger than its distance from boundary support, the supported ball is isometric to a Euclidean ball and multiplicity is one. The author calls this volume rigidity folklore. It is not a new operation here.

## n=2: exact consequence of the inverse-square source test

Normalize M(A)=4pi. For mu-a.e. y, the source03 test g=max(d_y,epsilon)^(-2), together with integer density, saturates the completed square. Fatou gives

  sqrt(1-|D d_y(x)|²)/d(x,y)=1/2

for mu-a.e. x distinct from y. In particular d(x,y)<=2 mu×mu-a.e., and the density at a good pole is one. This alone gives diameter<=2, not radius<=1, and does not directly give barycentric variance equality. No such inference is assumed.

A possible way to close the endpoint is the following **unverified geometric certificate**, to be checked against actual metric differentiation and primary equality arguments.

Choose a good density-one oriented chart point x and its Euclidean tangent plane E≅R² in the CAT(0) tangent cone C_xX. For almost every y, write v=log_x(y), r=|v|. Differentiability of d_y along the chart should imply that its first-variation functional on E is linear; the cone cosine formula would then imply

  d(v,z)²=|z-w_y|²+h_y² for all z in E,
  |w_y|²=r²-r^4/4,  h_y=r²/2.

If this exact distance identity puts v in the parallel set P(E)=E×N, the globally defined contraction

  f: X --log_x--> C_xX --projection--> P(E) --(w,n)↦(w,d_N(n,n0))--> R³

sends boundary support to the unit sphere centered (0,1). On boundary support it preserves distance from x, and its chart differential at x is the identity into R²×{0}. Constancy and a local oriented-density calculation should give f#A=±[S²]. Any minimizing filling S then pushes to ±[B³], by top-dimensional compact constancy. Choose p in spt S with f(p)=(0,1). Since f is1-Lipschitz and boundary images lie on the unit sphere, dist(p,spt A)>=1. Since M(S)=omega3, source-free monotonicity and Stadler rigidity would force a Euclidean ball.

The genuine current obligations are: (a) tangent differentiation into the actual tangent cone, not only an abstract metric differential; (b) the exact-distance-to-E implication for the parallel set; (c) no cancellation in f#A at the chosen regular pole; (d) primary overlap of this construction with classical Willmore/isoperimetric equality arguments. No claim is made until these are paid.

Source337 filling introduction and conclusion read in full; sections02 230–375,03 1–85 and290–365,04 1–105,05 380–525,06 1–210 read, with some earlier combined display truncation explicitly excluded from full-reading claims. Smooth companion08 150–250 read: its codimension-one punctured-flux identity yields a signed normal offset sphere and is a close antecedent to the contemplated certificate. Other acquired bodies remain unread except where a later ledger records exact ranges.

Myeongjin Kang. No affiliation. Original prose CC BY4.0.
