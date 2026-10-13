# I217 analytic attempts — partial

A. Seek a calibrated residual controlling distance to four allowed branch maps. Exact marginal domination is stronger than mere nonattainment; investigate its quantitative form without assuming a globally quadratic residual.

B. Seek exact measure-preserving rearrangements. Do not regularize Borel maps unless the output marginals are proved unchanged. First check the topological support obstruction: the central connected support has mass 1/3, each separated outer component mass 1/6, and a continuous central image must lie in one target component. If confirmed by the pinned interfaces, this rules out near-optimal Lipschitz maps altogether for this density, and leaves fractional/discontinuous complexity as a different task.

## Candidate bridge developed after first reading (not yet final)

Choose the source's free bump to be a product bump positive on a cube Ω compactly contained in B, and zero outside its closure. Let K be the union of its five image closures. Define Δ(T₂,T₃)=∫c_s(x,T₂,T₃)dμ−E_s(μ).

Candidate quantitative conclusions:

* BV complexity V=|DT₂|(Ω)+|DT₃|(Ω), or on all five component interiors, gives Δ ≥ c(1+V)^−2; exact cyclic maps give Δ≤C n^−2 and V≤Cn.
* For 0<t<1, 1≤p<∞, α=tp<1, fractional energy S=[T₂]_{W^{t,p}(Ω)}^p+[T₃]_{W^{t,p}(Ω)}^p gives Δ≥c(1+S)^−2/α. The same cyclic maps should have global/componentwise S≤C n^α. This would yield matching powers Δ∼S^−2/α, equivalently Δ∼norm^−2/t.
* W^{1,1}_loc maps have an absolute positive gap; no claim of integer-Sobolev approximation.

Lower mechanism: Sj={central x:T₂(x)∈Kj}, Fj=Hj^−1∘T₂. Exact preservation gives (Fj)#(ν|Sj)≤ν/2, including any incoming outer mass. The calibrated Hessian gives Δ≥a∑j∫Sj|Fj−x|²dν and Δ≥κν(S0)/3. Mollify χSj: its source/target testing discrepancy is ≥ν(Sj)/2; smoothing error is controlled by its BV or fractional perimeter, while the transport error is ≤C r^−1(ν(Sj)∫|Fj−x|²dν)^1/2. At least one outer Sj has mass≥1/8 if ν(S0)≤1/2. Optimizing r gives the candidate powers.

Upper mechanism: divide the first latent coordinate into n equal geometric cells. In each cell its conditional CDF q splits it at q=1/2. The increasing maps q↦2q (left half) and q↦2q−1 (right half) send the two restricted half-cell laws to one half of the whole-cell law. Their inverses Gk map the whole-cell law to twice the restricted law. Set T(x)=Yk(Fk(x)) on central half k; T(Yk(u))=Wk(u); T(Wk(u))=Gk(u). Then T³=Id almost everywhere and T#μ=μ exactly. Every triple is a permutation of (v,Yk(u),Wk(u)) with |v−u|≤2a/n. The calibrated residual is stationary at v=u, giving O(n^−2), with no first-order cost term. Monotonicity gives BV control even though inverse-CDF derivatives may diverge at flat bump endpoints. The branch jumps have total area O(n).

Novelty caution: the lower interpolation is an instance of established transport/mixing uncertainty; it cannot itself be claimed new. The possible contribution is its combination with this Coulomb certificate, exact cyclic recovery sequence, and sharp regularity regimes. Need complete details, literature comparison, and independent gates.
