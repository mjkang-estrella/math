# r50: unchanged T127N49, biased Walsh and two filtrations

The original full scope is byte-preserved from r49, SHA2560f7e6a7f6b600860b16015c8c6259646c68189340ec4a9f778a0f8c68dd57f87. r49 remains sealed. This continuation was requested by the parent after the r49 seal had just been written. No nomination or scope weakening.

Work in L2(mu) for the full-support biased product measure. Let V_r be degree<=r multilinear polynomials, V_{-1}=0. The biased Walsh basis has one constant and one centered normalized coordinate per factor. Set D=|P|^(1/2), after the source's sign-preserving constant perturbation removes zeros, and F=sign(P). Define TWO increasing filtrations

K_r^+=D V_r,
K_s^-=D(V_{n-s-1}^perp).

Both have dimension sum_{j=0}^r binom(n,j) at index r, because biased Walsh dimensions are binomial and symmetric. Both start at0 and end at the full space. Let E_r^+, E_s^- be their orthogonal increments, with projections Pi_r^+,Pi_s^-, and set M^+=sum(r-n/2)Pi_r^+, M^-=sum(s-n/2)Pi_s^-.

Multiplication by any Xi is a selfadjoint involution and maps either filtration up by at most one step. For the descending one, if b is orthogonal to V_{n-s-1}, then Xi b is orthogonal to V_{n-s-2}, since Xi maps that latter space into V_{n-s-1}. Thus the source's coordinate locality proof applies to each grading separately.

For a in V_r and b orthogonal to V_{n-s-1},

<Db,F Da>_mu=<b,P a>_mu=0 if r+s<n-d,

because Pa has multilinear degree<=r+d<=n-s-1. Therefore Pi_s^- F Pi_r^+=0 below this cross-grade triangle. Unlike inserting biased density into uniform parity, this argument is valid at every product bias.

F is still a selfadjoint UNITARY. Hence ||Pi_s^- F Pi_r^+||_HS^2/2^n defines a coupling whose two marginals are Bin(n,1/2), by ordinary trace and the two grade dimensions. For T=M^-F+FM^+,

2^(-n)||T||_HS^2=E(R+S-n)^2<=4d sqrt(n)

by source127's one-sided equal-law coupling lemma, applied to U=S,V=n-R. This is an exact cross-filtration extension of that coupling step. It does not yet bound the target pivotal sum.

Equivalent relation: K_s^-=(D^(-1)V_{n-s-1})^perp, so the minus grading is the reversed grading for D^(-1). Thus M^-=-M^+(D^(-1)), and T=F M^+(D)-M^+(D^(-1))F. In the fair case, parity conjugates the two filtrations and recovers the original source construction. For biased coordinates it is important not to assert that conjugacy by pointwise parity still holds.

At D=1, M^-=-M^+. In the normalized point basis, each local number operator has off-diagonal entry -sqrt(p_i(1-p_i)); its centered local diagonal entries are (1-2p_i)/2 and its negative. Consequently T=[F,M^+] detects a sign-changing edge with squared entry 4p_i(1-p_i), and ordinary Hilbert–Schmidt trace counts spectator assignments uniformly. The target uses sqrt(p_i(1-p_i)) times the PRODUCT probability of spectator assignments. Basis rotation alone does not change this trace.

The product vacuum is v=1 in L2(mu), or v_x=sqrt(mu(x)) in normalized point coordinates. Even the candidate recovery W<=C||Tv||^2 fails with an absolute C in the one-coordinate formal D=1 model: F=Xi gives W=sqrt(p(1-p)) while ||Tv||^2=4p(1-p). This example is also compatible with the actual choice P=Xi, since |P|=1. The ratio diverges as p tends to0. It refutes this particular squared vector-state recovery, not T127N49 and not every possible recovery inequality. A square-root recovery or a different quadratic form might still work, but no complete dimension/degree bound for it has been obtained.

## What the two-filtration estimate does not use

In fact the cross-filtration argument above works for ANY full-support law mu on the cube, not just a product law. Polynomial degree dimensions, multiplication locality, the perpendicular descending spaces, and ordinary trace all remain valid. Thus it cannot on its own encode the product assumption needed by T127N49.

An exact correlated-law obstruction makes this precise. Let n be even, let nu be uniform on the central slice sum Xi=0, and let mu=(1-eta)nu+eta U with 0<eta<1 and U uniform on the full cube. All marginals are fair and mu has full support. For the degree-one f=sign(sum Xi-1), under nu each coordinate's other-coordinate sum equals +1 or -1 equiprobably. Exactly the +1 case is pivotal, so I_i(nu)=1/2. Under mu, I_i>= (1-eta)/2. Hence the normalized pivotal sum is at least (1-eta)n/4, while the cross-filtration coupling still has the same O(sqrt(n)) energy bound. This is NOT a counterexample to the product-law target. It proves that an edge-recovery principle depending only on the two-filtration properties already proved, and not using further product structure, cannot suffice.
