# Frozen statement r232-Q

Quantitative flat point-on-side comparison from a bounded continuous distributional sectional defect.

Let n≥3 be an integer, n/3<p<∞, and v>0. Define
 α=p/(p+3n),
 B=5·4096^(n/p)/((3−n/p) v^(1/p)).
Let (X,d) be a complete separable metric space. Set m=H_d^n, with the same Hausdorff normalization as Source356. Assume full support and the UNREDUCED RCD(0,n) condition. Fix o∈X and assume
 m(B_r(x))≥v r^n for every x∈B_2(o) and every 0<r≤1.
All balls in this statement are open metric balls.

Use the nonpositive L²-generator Δ, and exactly the ORIGINAL GLOBAL classes
 Test(X)={f∈D(Δ): f has a bounded globally Lipschitz representative and Δf∈W^{1,2}(X)},
 TestV(X)={Σ_(j=1)^k a_j∇b_j: k<∞, a_j,b_j∈Test(X)}.
With [U,V]=∇_UV−∇_VU, the distributional curvature convention is
 R(U,V,Z,W)(f)=∫_X [−〈∇_U(fW),∇_VZ〉−f〈∇_VZ,W〉div U
                    +〈∇_V(fW),∇_UZ〉+f〈∇_UZ,W〉div V
                    −f〈∇_[U,V]Z,W〉] dm.
Let ρ:X→[0,1] be continuous. Assume, for EVERY U,V∈TestV(X) and EVERY nonnegative f∈Test(X),
 R(U,V,V,U)(f)≥−∫_X fρ (|U|²|V|²−〈U,V〉²) dm.
Set δ=(∫_(B_3(o)) ρ^p dm)^(1/p).

Then for EVERY a,x,y∈B_1(o) satisfying
 d(a,x)+d(x,y)+d(y,a)≤1,
EVERY constant-speed minimizing geodesic σ:[0,1]→X from x to y, and EVERY t∈[0,1],
 d(a,σ_t)²≥(1−t)d(a,x)²+t d(a,y)²−t(1−t)d(x,y)²−22(Bδ)^α.
The final error is interpreted as zero when δ=0. Degenerate triangles and constant sides are included. No chosen side or exceptional set is omitted.

This is a normalized local additive comparison estimate, not a Gromov–Hausdorff approximation assertion, a sharp-exponent assertion, or a theorem for unbounded/measurable defects, weighted reference measures, collapsed limits, or incomplete spaces. Its proof may use Source356 and every operative upstream proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb as stipulated true. This statement assigns no correctness, contribution, acceptance or count.
