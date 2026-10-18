# Route A: Cotlar along the flow and the unpaid curvature comparison

Author research only. The target is every planar unit Lipschitz field with Lip(v)≤1, every complex Schwartz input, and an absolute short outer length a, with the supremum over all0<ε<a INSIDE L2. We do not replace its straight segments by flow curves.

## What classical Cotlar actually pays

Let Φ_t be the global ODE flow of v and define

    J_a^ε f(z)=∫_{ε<|t|<a} f(Φ_{−t}(z)) dt/t,    J_a^*=sup_ε |J_a^ε|.

For a≤1/10, this maximal operator is uniformly L2-bounded, without source083. Here is the elementary local transference proof, so no measure-preservation hypothesis is hidden. The flow and its inverse are e^{|t|}-Lipschitz, so their area Jacobians lie between e^{−2|t|} and e^{2|t|} almost everywhere. Fix z and set g_z(s)=1_{|s|≤2a}f(Φ_s(z)). For |s|≤a, the local maximal one-dimensional Hilbert transform of g_z equals J_a^*f(Φ_s(z)). Denote the L2 norm of the one-dimensional maximal double-truncation operator by C_H. Integrating its inequality in z gives

    2a e^{−2a} ||J_a^*f||2²
      ≤ ∫dz ∫_{−a}^a |J_a^*f(Φ_s z)|² ds
      ≤ C_H² ∫dz ∫_{−2a}^{2a}|f(Φ_s z)|² ds
      ≤ 4a C_H² e^{4a} ||f||2².

Thus ||J_a^*||2→2≤sqrt(2)e^{3a}C_H. The flow and change-of-variables facts follow from Grönwall and the area formula for bi-Lipschitz maps; neither a smooth invariant density nor straight trajectories is assumed. Rational cutoffs suffice for Schwartz inputs.

The read author notes of Hajłasz prove the one-dimensional Cotlar inequality in Lemma5.15, then maximal Lp boundedness in Corollary5.16; the proof of(7.7) handles both endpoints. This is a standard paid operation, not a new contribution. The one-dimensional identity is applied to s↦f(Φ_s z), not to the frozen-line operator at other points.

## Exact defect of the tempting substitution

Write F_t(z)=z−tv(z). The flow has the group law, but the frozen maps have only

    |F_t(F_s z)−F_{t+s}z|
      = |t| |v(z)−v(z−sv(z))| ≤ |ts|.

Moreover |F_t(z)−Φ_{−t}(z)|≤t²/2. A physical displacement bound is not an L2 operator-norm bound on arbitrary inputs. For a≤1/10, the interpolating maps G_{t,θ}=(1−θ)F_t+θΦ_{−t} obey Lip(G_{t,θ}−Id)≤e^a−1<1. Thus composition with G_{t,θ} has L2 norm at most (2−e^a)^(−1). The fundamental theorem of calculus yields

    ||f∘F_t−f∘Φ_{−t}||2 ≤ t²/[2(2−e^a)] ||∇f||2.

Consequently the maximal comparison error

    E_a^*f = sup_{0<ε<a}|H_{v,a}^ε f−J_a^ε f|

satisfies ||E_a^*f||2≤a²/[2(2−e^a)]||∇f||2. For a Fourier-supported input |ξ|≤R this costs C a²R||f||2. Combining with the uniform fixed-time composition bound gives, by integrating min(C,Ct²R)/|t|,

    ||E_a^*f_R||2 ≤ C[1+log_+(a sqrt(R))] ||f_R||2.

No uniform frequency summation follows. Source083 bounds each H_{v,a}^ε, hence each fixed difference H−J; it does not bound their supremum. The missing estimate is precisely

    sup_{Lip(v)≤1, |v|=1} ||E_a^*||2→2 ≤ C                 (A)

at one absolute a>0, with C independent of frequency, all cutoffs and v. Given the flow estimate, (A) is equivalent up to an additive absolute constant to the full target. We have not proved(A).

## A concrete non-small curvature error

A stronger absorption proposal ||E_a^*||≤Ca is FALSE. Take the globally smooth unit field v(x,y)=(cos x,sin x), with Lip(v)=1. Under x=aX,y=a²Y and t=as, the frozen maps tend, uniformly on compact sets, to

    (X,Y)↦(X−s,Y−sX),

whereas the flow maps tend to (X−s,Y−sX+s²/2). This follows directly from the scaled flow equations X'=cos(aX), Y'=sin(aX)/a and uniform convergence to X'=1,Y'=X on compact time/space sets. In the coordinate Q=Y−X²/2 the respective limits are

    (X,Q)↦(X−s,Q−s²/2),       (X,Q)↦(X−s,Q).

Choose a fixed C∞ cutoff χ equal1 on[−2,2], supported in[−3,3], 0≤χ≤1. Set F(X,Q)=χ(X)χ(Q)exp(iX+iQ) and the compactly supported smooth

    f_a(x,y)=F(x/a, y/a²−x²/(2a²)).

Its L2 norm is a^(3/2)||F||2. Consider the difference of frozen and flow transforms on a/4<|t|<a/2. At scaled origin its limit is

    L=−2i∫_{1/4}^{1/2} sin(s)[exp(−is²/2)−1] ds/s.

The real part is negative, and

    −Re L = 2∫ sin(s)sin(s²/2) ds/s ≥ ∫_{1/4}^{1/2}s² ds/4 = 7/768.

We used sin(s)≥s/2 and sin(s²/2)≥s²/4 on that interval. Continuity gives a fixed positive-area output neighborhood where the limit modulus is at least7/1536. Compact uniform convergence of the maps and integrands gives a positive lower bound c||f_a||2 for the L2 norm of the annular difference, for all sufficiently small a. The difference of E_a^{a/4} and E_a^{a/2} is that annular error, so ||E_a^* f_a||2≥(c/2)||f_a||2. No uniform O(a) bound is possible.

This construction is not a counterexample to(A) or to the maximal theorem. It identifies the non-negligible transverse frequency scale a^(−2). A successful flow proof must handle that parabolic-scale cancellation, not discard curvature as a small L2 perturbation. For merely Lipschitz fields the O(t²) flow displacement remains available, but no uniform higher Taylor remainder is supplied. No general variable-curvature maximal estimate is imported without its actual hypotheses.
