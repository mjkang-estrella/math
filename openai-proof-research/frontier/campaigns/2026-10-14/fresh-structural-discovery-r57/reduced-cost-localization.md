#Reduced-cost localization for W152 — working author proof

This is a proposed repair of the unchanged prior W152 interface, not a new scope freeze or contribution verdict.

Let Ω={x∈Z^E: Bx=b,0≤x≤u} be a nonempty bounded integral network-flow fiber (in particular a cell-bounded table). Activities θ_e>0 are rational. The desired weight is w(x)=∏θ_e^{x_e}. Let N0=∏(u_e+1) and U=∑u_e; both have polynomial binary representations. To total multiplicative tolerance exp(±η), approximate c_e=−log2θ_e by rational ĉ_e within η/[(1+U)log2], using polynomially many precision bits because log U is polynomial. Then |log w(x)+log2·ĉ·x|≤η for every feasible x. There is no loop of length U.

Minimize ĉ·x over the bounded flow polytope. Integral flow optimization and an exact rational dual provide an integral optimum x*, vertex potentials π, reduced costs r_e=ĉ_e−(Bᵀπ)_e, and optimum value
C*=π·b+∑_{r_e<0}r_e u_e.
Complementary slackness gives x*_e=0 if r_e>0 and x*_e=u_e if r_e<0. Thus, for every feasible x,
ĉ·x−C*=∑_{r_e>0}r_e x_e+∑_{r_e<0}(−r_e)(u_e−x_e)=:g(x)≥0.
The endpoint choices ARE simultaneously feasible: x* witnesses them. Zero reduced costs impose no endpoint choice.

Choose integer K≥log2 N0+log2(1/δ). For r_e>0 replace the upper bound by min(u_e,floor(K/r_e)); for r_e<0 replace the lower bound by max(0,u_e−floor(K/(−r_e))); leave r_e=0 unchanged. This box contains x* and every feasible table with g(x)≤K. Its excluded tilted mass is at most N0·2^(−C*−K)≤δ·2^(−C*)≤δ Z_hat, where Z_hat=∑Ω2^(−ĉ·x). Hence truncation changes the normalized law by at most δ and the normalizer by at most a δ fraction. Tiny nonzero reduced costs cause no difficulty: exact rational division/flooring uses polynomial binary lengths; if K/|r_e| exceeds u_e the bound remains unchanged.

For each cell throughout the truncated physical box, its nonnegative gap contribution q_e lies in[0,K]. Therefore the whole reduced objective g lies in[0,|E|K], uniformly over all box points, including those not satisfying margins. Subsequent ordinary endpoint tightening can only shrink this interval and its coefficient-times-width bounds |r_e|b_e≤K. Translation contributes a computable constant. The source's large-cell forest may now be selected using the tightened capacities, as in the original construction.

On the source's extended tree intervals, a tree coordinate lies between−10db_t and10db_t after translation. Since |r_t|b_t≤K and its physical endpoint contributions lie in[0,K], each unary linear contribution is between−10dK and(10d+1)K. Free/small coordinates remain in their boxes. Thus the total reduced objective on EVERY profile/free assignment required by the source has absolute value O(d²K), independently of numerical capacities.

The normalized-coordinate Lipschitz bound also survives. The source forest cut identity gives |Δz_t|≤2db_t||Δu||∞ for fixed small profile. Multiplying by |r_t|, summing≤d tree terms and adding free terms bounds |Δg|≤(2d²+d)K||Δu||∞. This is polynomial, not proportional to original capacity times log activity.

Potential source adaptation (not yet complete): add this affine g and a fixed polynomial offset B0 to the source convex soft penalty D, and anneal the sum P=D+g+B0 from the unweighted initial j=0 law. Choose B0 to make P≥0 on all required extended profiles; its range and Lipschitz constant stay polynomial. The integer-signature lemma allows additional unary exponential factors. The endpoint-marginal contamination proof uses only the logarithm of the ratio between maximum mass and positive attainable endpoint masses, so the above O(d²K) range can enter its budget. Bin conductance uses log-concavity plus polynomial normalized Lipschitz bounds. These observations identify precise source contracts; full parameter consistency, defect ratios, finite arithmetic, weighted self-reduction and compact normalizer output still need a complete check.

This is not an impossibility result for old W152, not a proof of every source adaptation, and not a novelty claim. The log approximation/flow dual/truncation may be a standard technical transfer; actual primary comparison comes before any nomination.
