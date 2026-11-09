# Prefreeze compatibility calculation

This calculation precedes freezing the proposed quantitative statement. It is a smooth example, not a theorem asserting a nonsmooth conformal change of an RCD structure.

Take M=S²×S² with both factors unit round and product metric g. Its dimension and tangent rank are 4, Ric_g=g, and its sectional curvatures lie in [0,1]. At a point b choose g-normal coordinates on a fixed ball. Fix a nonnegative smooth function φ supported in the Euclidean unit ball which equals |z|²/2 near 0. For sufficiently small ε>0 put u_ε(x)=a ε² φ(x/ε) in the coordinate chart and zero elsewhere, and g_ε=e^{2u_ε}g.

There is a finite C≥1 independent of a∈(0,1] and ε∈(0,ε₀] such that |u_ε|≤Caε², |du_ε|_g≤Caε, and |Hess_g u_ε|_g≤Ca. This follows directly from ∂u=aε∂φ, ∂²u=a∂²φ, the bounded coordinate metric and inverse metric, and Hess_ij u=∂ij u−Γ^k_ij∂k u. Reduce ε₀ so the chart closure is compact and Cε₀²≤1. Fix a>0 small enough for all inequalities below.

For completeness, Koszul's formula applied to e^{2u}g gives
 ∇^u_XY=∇_XY+du(X)Y+du(Y)X−g(X,Y)∇u.
Substituting this difference tensor into R^u=R+d^∇A+A∧A gives, for g-orthonormal X,Y,
 K_{g_u}(span{X,Y})=e^{−2u}[K_g(X,Y)−Hess u(X,X)−Hess u(Y,Y)+du(X)²+du(Y)²−|du|²].
Tracing in a g-orthonormal basis gives, in dimension4,
 Ric_{g_u}=Ric_g−2(Hess u−du⊗du)−(Δ_g u+2|du|²)g.
Here the trace convention Δ_g=tr Hess has nonpositive spectrum. The trace is of the transformed curvature after using the transformed orthonormal basis e^{−u}E_i; no reference-measure reweighting is being mistaken for a change of metric.

The negative part of the Ricci perturbation is bounded in quadratic-form norm by 6Ca+2C²a²ε₀². Choose a so this is ≤1/2. Then Ric_{g_ε}≥g/2>0. The sectional lower bound is ≥−e^{2Caε₀²}(2Ca+C²a²ε₀²); reduce a once more so this is ≥−1. At b, u=du=0 and Hess u=a g. A mixed two-plane therefore has K_{g_ε}=−2a<0 for every ε.

Let ρ_ε(x)=max{0,−min_{Π⊂T_xM, dimΠ=2} K_{g_ε}(Π)}. The minimum over the compact Grassmannian varies continuously, so ρ_ε is continuous, lies in [0,1], and vanishes outside the coordinate ε-ball. Put m_ε=H^4_{d_{g_ε}}. With the same Hausdorff normalization throughout this is Riemannian volume (or its fixed conventional factor), and dm_ε=e^{4u_ε}dm_g. In particular ||ρ_ε||_{Lp(M,m_ε)}≤C_p a ε^{4/p}→0 for every finite p. The smooth curvature formula, integrated against the original global test functions, gives exactly the required tensor inequality with ρ_ε. Compactness makes all such integrals finite, and the nonsmooth test identity is the closure of the smooth integration-by-parts formula in the fixed graph/Sobolev norms; this is the source calculus interface, not an assumed pointwise tensor for a singular space.

The length metric d_{g_ε} is complete because M is compact. It is uniformly bilipschitz to d_g since |u_ε|≤Caε₀². Full support holds, both Hausdorff and tangent-module dimensions are4, and the Ricci bound gives the unreduced RCD(0,4) condition with this exact Hausdorff measure. If L=e^{Caε₀²}, then B^{g_ε}_r(x) contains B^g_{r/L}(x) and m_ε≥L^{−4}m_g. On the fixed compact smooth manifold inf_{x,0<s≤1}m_g(B_s(x))/s^4 is positive: use uniform normal-coordinate bounds for small s and compactness for the remaining scales. Hence m_ε(B^{g_ε}_r(x))≥v r^4 for a single v>0 and all x, 0<r≤1, uniformly in ε.

This verifies that the proposed joint hypotheses admit a sequence with nonzero negative sectional curvature, a fixed positive noncollapse constant and defect norm tending to zero. The free small parameter is real; no normalization forces ρ=0. This is not a sharpness example for the proposed exponent.
