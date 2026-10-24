# Integrated concentration calculation (prefreeze derivations, not a nominee)

This is one fixed exact Source352 flow, with fixed gluing parameters and its fixed delta in (0,1). Constants below may depend on that flow. No uniform family, perturbation openness, or additional profile parameter is asserted. Time is shifted so its singular time is 0, t<0, rho=sqrt(-t). Complex dimension n=10, physical real dimension 20, auxiliary analytic dimension 24. All Source352 operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## 1. The actual estimate and radial jets

Write v=x(1-x)[1+x(1-x)H], H=F+V, F=(G(x/rho)-1)/x, b=1+x(1-x)H. The source gives b bounded above and away from zero, and the weighted four-space/one-time-derivative estimate for V with weight sigma^(-2+2delta), sigma=(x+rho)^(1/2). Consequently, for j=0,1,2,

    |d_x^j V| <= C (x+rho)^(-1+delta-j).                 (1)

This uses the auxiliary smooth radial lift, not the physical metric. If z is an auxiliary point with |z|^2=x and e is a unit tangent to its Euclidean sphere, then d_e^2 V=2V_x and d_e^4 V=12V_xx. The same identities hold at z=0 and, with opposite first-derivative sign, in the other endpoint chart x=1-|w|^2. Interior charts give equivalent bounded estimates. This extracts both derivatives from the supplied four-derivative norm. Also |V_t|<=C(x+rho)^(-3+delta). The full differentiated source asymptotics imply |d_x^j F|<=C_j(x+rho)^(-1-j).

The source scalar convention is S=tr_omega Ric and omega=i ddbar Phi. Set K0(H)=110H+22xH_x+x^2H_xx. Direct expansion gives

 K(H)=(110-264x+156x^2)H
       +(22x-48x^2+26x^3)H_x
       +(x^2-2x^3+x^4)H_xx.

Thus |(K-K0)F|<=C and |K(V)|<=C(x+rho)^(-1+delta). Define

 R(y)=-y^(-9)[y^10(G(y)-1)]''
     =90(1-G(y))/y-20G'(y)-yG''(y).

Then, on the entire momentum interval, including both endpoints by extension,

 S(t,x)=rho^(-1) R(x/rho)+E(t,x),
 |E(t,x)|<=C[1+(x+rho)^(-1+delta)].                    (2)

The source origin slope and tail give

 R(0)=-110G'(0)>0,
 R(y)=A/y+O(y^-3), A=90(1-c)>0, c=(1+d)^(-1).

In particular |S|<=C/(x+rho). The lower bounds below do not follow from this upper bound: they use R(0)>0 and A>0 independently.

## 2. Evolving measure, supercritical moments, and the critical logarithm

For dmu=omega^n/n!, its radial pushforward is

 dmu=C_n x^(n-1)dx, C_n=(2pi)^n/(n-1)!.

Indeed det(g)=x^(n-1)v/q^n and Euclidean polar integration gives (2pi)^n x^(n-1)v dq/[(n-1)!q]; dx=v dq/q. Hence volume=(2pi)^n/n!, and the probability volume pushes to n x^(n-1)dx. These are evolving-volume statements; fixed background volume has different asymptotics.

For every fixed real p>n=10, (2), x=rho y, and dominated convergence yield

 lim_{t up to 0} rho^(p-n) integral |S|^p dmu
   = C_n integral_0^infinity |R(y)|^p y^(n-1)dy =: I_p in (0,infinity).   (3)

For domination, rho|S(t,rho y)|<=C/(1+y), extended by zero for y>1/rho; this is integrable to the p-th power precisely when p>n. The limit is positive on a fixed core interval because R(0)>0. In particular (3) is a two-sided asymptotic, not an inferred lower bound from an upper estimate.

At p=n, use the elementary difference bound

 ||a+e|^n-|a|^n| <= C_n(|a|^(n-1)|e|+|e|^n).

The contribution of E to the difference of integrals is uniformly bounded: its worst term is bounded by a constant times integral_0^1 x^(n-1)(x+rho)^(-n+delta)dx, and the analogous n delta power term is also bounded. The main term is C_n integral_0^(1/rho)|R(y)|^n y^(n-1)dy. Its tail differs from A^n/y by O(y^-3). Therefore

 integral |S(t)|^10 dmu = C_10 A^10 log(1/rho)+O(1).                  (4)

The critical L^10 norm is unbounded. For 0<p<10 the moments are uniformly bounded. At p=10 there is nevertheless a uniform weak-L^10 bound:

 mu{|S|>lambda} <= (C_n/10) min(1,(C/lambda)^10).

For p<10 the bound is not offered as a new regularity failure theorem by itself; it is a direct complete application of the paid weighted construction. Formula (4) also shows why one cannot strengthen it to bounded strong L^10 for this example.

## 3. Exact spacetime threshold

For p>10, (3) yields integral |S|^p dmu ~ I_p rho^(10-p). Since dt=-2rho d rho, the scalar spacetime integral near 0 converges exactly for p<12. At p=12 it diverges logarithmically; for p>12 it diverges by a power. The bounded p<10 moments and the logarithmic p=10 estimate handle the remaining exponents. Thus, for this fixed solution and any t0<0,

 integral_{t0}^0 integral |S|^p dmu dt < infinity  iff  0<p<12.        (5)

This uses physical dimension 20 and fourth-order time scaling. The number 24 in the auxiliary flat operator is not the physical volume dimension. For p=12 the leading divergence from a lower time cutoff -epsilon is I_12 log(1/epsilon)+o(log(1/epsilon)); the factor 2 from dt and log(1/sqrt(epsilon)) cancel.

## 4. Localization is a separate geometric step

Equations (2)-(5) control the entire compact manifold, so no unestimated exterior energy is hidden. They initially describe the time-dependent momentum coordinate. They do not alone locate concentration in a fixed complex chart. The separate fixed-gauge calculation in 03-terminal-geometry.md shows that x shrinking to zero localizes at the fixed projective point p, and that compact subsets of x>0 have uniformly regular fixed-coordinate limits. With that calculation, the measures

 [log(1/rho)]^(-1) |S|^10 dmu

converge weakly to C_10 A^10 delta_p. For a continuous test function, first bound the x>=epsilon mass by O_epsilon(1)/log(1/rho), and then use uniform localization of x<=epsilon at p and the total mass asymptotic (4), finally epsilon down to 0.

## 5. Comparison and limits

Li-Zhang-Zheng v2 extends a finite-time flow with uniform evolving-volume L^p scalar curvature for p>n, using entropy and elliptic estimates. This constructed flow has divergent L^p for every such p. Li-Zhang II v2 assumes a spacetime integral of (Delta S)_+^(p+1)+|S|^(2p), p>n; its scalar term already diverges here because 2p>20>12. It is not a scalar-only spacetime criterion at p>n. The positive-part notation in the Delta term was visually recovered from PDF page 2 after imperfect first extraction/crop.

These computations execute the strongest immediate concentration consequence of the source. No claim is made that integration of its paid estimates is an independently substantial contribution, or that these thresholds are universal over arbitrary Calabi flows. A distinct continuation construction is examined separately; no theorem has been frozen.
