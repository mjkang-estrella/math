# I222 — independent proof review of Coulomb cost-complexity

**Verdict: PASS, at the exact scope stated below.** No mathematical correction to the submitted theorem is required. This is an independent proof verdict, not a contribution, priority, or acceptance-count decision. I221 and other active reviews were not read, and no outcome from them is presumed.

An early partial record was written after reading the complete source and before completing the measure, extension, and sharpness checks. This final record supersedes that provisional assessment.

## 1. Exact scope of the pass

For each fixed integer d>=2 and real s>0, take the source's local branches and a cube Q=(-a,a)^d compactly inside its common central ball. Use precisely the displayed product bump g=C product_i exp(-1/(a^2-x_i^2)), zero outside Q, with integral g^2=1. Put nu=g^2 dx and

    mu=nu/3+(Y_1#nu+W_1#nu+Y_2#nu+W_2#nu)/6.

For all Borel pairs individually preserving mu, the asserted lower bounds hold with unweighted Lebesgue complexities on Q:

    Delta >= c(1+V_Q)^(-2),
    Delta >= c_{t,p}(1+S_Q)^(-2/(tp))  if 0<t<1, 1<=p<infinity, tp<1.

Here V_Q is the sum of the variations of the two maps, and S_Q is the sum of their pth Gagliardo seminorms, as defined in I220. Nonfinite complexity is assigned +infinity, making the corresponding lower bound zero. Only T_2's central complexity is needed.

There is one explicitly defined sequence T_n, independent of t,p, preserving mu and satisfying T_n^3=Id mu-a.e. Its actual square preserves mu. Both maps have bounded compactly supported Borel representatives, and

    0<Delta(T_n,T_n^2)<=C n^(-2),
    |DT_n|(R^d)+|D(T_n^2)|(R^d)<=C n,
    [T_n]_{W^{t,p}(R^d)}^p+[T_n^2]_{W^{t,p}(R^d)}^p<=C_{t,p} n^(tp)

for each fixed 0<t<1, 1<=p<infinity, tp<1. Constants depend on the fixed geometry and bump, hence can depend on d,s; fractional constants also depend on t,p. No uniform limit in s, d, t, or p is included.

A preserving T_2 continuous on Q, in W^{1,1}_loc(Q), or of finite W^{t,p}(Q) seminorm with 0<t<1, 1<=p<infinity, tp>=1 has a fixed positive gap Delta>=kappa/3. The same statement does not require T_3 to have these regularities.

The resulting constrained infima have the claimed matching powers, for sufficiently large budgets, on Q, componentwise on the five open components, on their union, or globally. This remains true if the infimum is restricted to the preserving order-three maps (T,T^2). The conclusions do not extend here to an arbitrary nonproduct bump, weighted fractional energies, smooth recovery, exact leading coefficients, regularized minimizer existence, or a Gamma-limit.

## 2. Actual source interfaces and all d,s

I read all 749 lines of the existing full manuscript extraction, including its references. In particular:

- Lemma 3.1 and its proof, source pp. 4–5: the Hessian is in (x,z) while the positive outer variable y is fixed. Its stationary pair is (X_k(y),Z_k(y)), and the strict-convexity region is a product of balls.
- Proposition 4.1, p. 6: the entire contact set consists precisely of the two branch families and their permutations. Other component types have strict gaps, including repeated-component types.
- Lemma 4.2 and Section 5, pp. 7–8: the common central ball, the diffeomorphisms Y_k and W_k, smooth density and square root, the exact coefficients 1/3 and 1/6, and E_s(mu)=3 integral u dmu.
- Section 6, pp. 9–11: the existing approximation and measurable-map interfaces. I do not treat its qualitative approximation as the new regularity estimate.
- Theorem 7.1 and its full proof, pp. 11–13: the same strict-convexity, diffeomorphism, contact, and smooth-density construction for every d>=2,s>0. The eigenvalues s(s+1)|b|^(-s-2) and -s|b|^(-s-2) are nonzero for every s>0; the source's construction constants may depend on d,s.

Source results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. I independently checked the new deductions using these interfaces. A fresh retrieval of the pinned PDF, streamed through pdftotext -layout and SHA256, matched the complete existing extraction: 0c82801c83218d368b0edf839a3f4c32f3c3998a53e4e0d1dba3c96465ca5efe. No new source copy was needed.

Let K_0=Qbar and K_j=H_j(Qbar), with H_1=Y_1,H_2=W_1,H_3=Y_2,H_4=W_2. They are compact and separated inside the source's open components. The product bump is C_c^infinity on that ball, flat also at cube corners; the source's change-of-variables formula therefore gives the asserted smooth rho and sqrt(rho). The density is positive throughout each open component D_j=H_j(Q), but not bounded below up to its boundary.

For either k, take slightly larger compact subproducts inside the source's strict-convexity balls. Continuity of the Hessian gives a positive uniform lower eigenvalue lambda there. The segment joining (x,z) to the stationary pair stays in the convex product of the x- and z-balls, even though W_k(Qbar) itself need not be convex. Consequently

    R(x,Y_k(v),z) >= (lambda/2)(|x-v|^2+|z-W_k(v)|^2).

This proves the bound for the selections Y_1,Y_2. For selection W_k, write the other outer coordinate as Y_k(v) and the selected coordinate as z=W_k(t), and permute the triple before applying this bound. With L_k=Lip(W_k^{-1}|K_{W_k}),

    |x-t|^2 <= 2 max(1,L_k^2)(|x-v|^2+|W_k(t)-W_k(v)|^2).

This yields the claimed lambda/(4 max(1,L_k^2)) coefficient for W_1 and W_2. It does not assert positivity of a different Hessian with the negative outer variable fixed.

On every forbidden compact component product, R is lower semicontinuous, is infinite at collisions, and has no zero by the stipulated complete contact characterization. It attains a strictly positive minimum. There are only finitely many such products. Their minimum kappa, together with |x-H_j^{-1}(y)|<=diam(Q), gives exactly the uniform a_0 bound in I220. In particular, when x and T_2(x) are both central, R>=kappa regardless of T_3. No condition s<d is used: upper triples stay separated, and infinite lower costs are permitted.

## 3. Measures, completion, and the lower bounds

For Borel S_j={x in Q:T_2(x) in K_j}, the restricted map F_j=H_j^{-1}T_2 is Borel. For every Borel A subset Qbar, H_j(A) is Borel: H_j is a homeomorphism between these compact sets, also the restriction of a diffeomorphism. Separation of all five components gives

    (1/3)nu(S_j intersect F_j^{-1}(A))
       <= mu(T_2^{-1}(H_j(A)))
        = mu(H_j(A)) = (1/6)nu(A).

Thus beta_j=(F_j)#(nu|S_j)<=nu/2 as measures, not merely in total mass. Incoming outer mass cannot invalidate this inequality. This proof also extends the domination to completed measurable sets: use Borel representatives and null envelopes. The theorem itself is stated for Borel maps, so no non-Borel image assertion is required.

Since f=g^2>0 at every point of Q, nu-null and Lebesgue-null sets in Q coincide. One can prove the nontrivial implication by exhausting Q with {f>=1/m}. The same holds on D_j by change of variables. This justifies identifying the Borel labels with their BV or fractional equivalence classes. It does not identify null sets outside the support with Lebesgue-null sets, and the proof never needs that false assertion.

Integrating the calibration yields

    Delta >= (a_0/3) sum_{j=1}^4 E_j,   E_j=integral_{S_j}|x-F_j(x)|^2 dnu,
    Delta >= (kappa/3)nu(S_0).

If nu(S_0)>=1/2, the lower bound is already fixed. Otherwise some outer selection S has m=nu(S)>=1/8. Let phi=eta_r*1_S, with the indicator zero-extended, and e=integral|phi-1_S|dnu. Direct calculation gives

    integral phi d(nu|S-beta) >= m/2-3e/2,
    |integral phi d(nu|S-beta)| <= (||grad eta||_1/r)sqrt(mE).

Indeed the first term is at least m-e, and domination bounds the subtracted term by (m+e)/2. If e<=m/6, then E>=mr^2/(16||grad eta||_1^2)>=r^2/(128||grad eta||_1^2). This verifies the constants as well as the exponent.

Choose a bounded Lipschitz label equal to one on K_j and zero on the other K_i, with Lipschitz constant at most 2/delta_K. Its composition with T_2 equals 1_S a.e. on Q. The BV chain rule bounds its variation by L|DT_2|(Q). Zero extension from the cube contributes at most its boundary area, because the trace is bounded by one. Thus mollification error in Lebesgue L^1 is at most C r(L|DT_2|(Q)+H^{d-1}(boundary Q)).

For fractional regularity, the binary label has |chi(x)-chi(y)|=|chi(x)-chi(y)|^p. Hence its W^{alpha,1}(Q) energy, alpha=tp, is at most L^p[T_2]_{W^{t,p}(Q)}^p. Zero extension contributes no more than

    2 integral_Q integral_{R^d\Q}|x-y|^(-d-alpha) dy dx.

This is finite for alpha<1: the inner integral is bounded by C dist(x,boundary Q)^(-alpha), and boundary layers of a cube have volume O(r). The full-space Gagliardo formula then bounds mollification error by C r^alpha times that extended energy. Both these boundary terms are necessary and are present in I220.

Finally e<=||f||_infinity times the unweighted L^1 error. Choosing r of order (1+V)^(-1), respectively (1+S)^(-1/alpha), makes e<=1/48<=m/6. This proves the stated lower powers, including p=1, without ever dividing by the flat density. The constant in the large-m_0 alternative can be combined with the small-m_0 constant as in the submitted proof.

## 4. Exact recovery and actual powers

The product assumption is used essentially here. On each geometric interval I_l, the normalized marginal CDF q_l is strictly increasing, continuous on the closed interval, and smooth in its interior. Its two probability halves each have half the cell mass. CDF doubling on either half and the inverse maps give, for k=1,2,

    F_k#(nu|A_k)=nu/2,    G_k#nu=2nu|A_k,
    F_k G_k=Id,          G_k F_k=Id

on full-measure sets, with displacement at most h=2a/n. The transverse product law is unchanged. These formulas remain valid at the first and last cells even though the density vanishes to infinite order at the exterior endpoints: invertibility on the open interval and endpoint limits suffice. Equal geometric half-lengths were not assumed.

Define T by the three legs in I220. The mass transformations for each k are exactly

    nu|A_k/3 -> (Y_k)#nu/6 -> (W_k)#nu/6 -> nu|A_k/3.

Their sum is mu, so T#mu=mu. The cycles close a.e., hence T^3=Id a.e. and (T^2)#mu=mu. The formulas for both powers on each component in I220 are correct; in particular T^2(Y_k(u))=G_k(u) and T^2(W_k(u))=Y_k(u) a.e.

A fully specified admissible choice is zero on all unassigned cell/half-cell planes, their relevant component images, and the support boundaries; zero outside K; and T(0)=0. These are Borel null exceptional sets. Any further version choices should also be on Borel null sets (or replaced by such envelopes). A change on a mu-null set N changes the square only on a subset of N union T^{-1}(N), which is mu-null for the original preserving map. On the interiors of the five components this is also Lebesgue-null. Outside K, T^2(x)=T(0)=0 exactly. Thus the assertion concerns the actual full-space composition, not an independently selected representative of its a.e. class. The point modification does not damage BV or fractional estimates.

For R=c_s-sum u, the central derivative vanishes at (u,Y_k(u),W_k(u)); this is source stationarity, also implied by smooth nonnegativity near this contact point. Along the segment from u to v with the two outer coordinates fixed,

    0<=R(v,Y_k(u),W_k(u))<=H_*|v-u|^2/2.

All segments remain in the central cube and all pair distances stay positive. The full cost excess can equivalently be written

    Delta(T,T^2)=(1/2) sum_{k=1}^2 integral R(G_k(u),Y_k(u),W_k(u)) dnu(u),

using the three leg weights and symmetry. It is bounded by H_*h^2/2. There is no uncancelled first-order contribution from the physical cost or the potential: the residual is the correct quantity to expand. Strict positivity also follows from the proved lower BV bound.

## 5. Global BV, interfaces, and fractional support crossings

On each central half-box, the scalar first-coordinate map is increasing and takes values in its original cell. Its total variation is at most h. It is smooth internally and has endpoint limits; unbounded inverse-CDF derivatives cannot increase this total variation. The other coordinates are identities. Consequently the sum of interior variations over the 2n boxes is bounded independently of n. Postcomposition with the fixed smooth branches preserves this bound up to fixed factors.

On the outer components, precomposition with H_j^{-1} likewise multiplies the interior estimates by fixed factors. This can be seen directly by changing variables in the interior derivative integral: both Jacobians and derivatives are bounded on compact neighborhoods. The same reasoning applies to all six formulas for T and T^2 listed in I220.

There are O(n) central interfaces, each with bounded (d-1)-area and bounded jump size. The outer cell interfaces are images under the fixed diffeomorphisms, so their areas also have uniform bounds. Their number is O(n). The jumps of G_k across cell boundaries are actually at most h, but an O(1) bound suffices.

Each D_j is the diffeomorphic image of a cube with closure in the smooth coordinate chart. It is a bounded Lipschitz domain; in particular it has finite perimeter. The piecewise maps have bounded traces. Extending them by zero adds at most a fixed bound for the trace times the sum of these five perimeters. Intersections of faces, edges, and internal interfaces have codimension at least two and do not add a (d-1)-dimensional jump term. Thus both actual powers have total full-space variation O(n), bounded support, and uniformly bounded L^1 and L^infinity norms.

For either U=T or T^2, the full-space BV translation inequality gives

    integral |U(x+z)-U(x)|^p dx
      <= (2||U||_infinity)^(p-1) min{|z||DU|(R^d),2||U||_1}
      <= C min{n|z|,1}.

Integrating against |z|^(-d-alpha) and splitting at 1/n gives

    [U]_{W^{t,p}(R^d)}^p <= C n^alpha(1/(1-alpha)+1/alpha).

This proof includes every support-boundary and cross-component interaction. It is not an inference from componentwise fractional bounds alone. It also covers p=1. Constants need not remain bounded as alpha approaches zero or one.

## 6. Rigidity, including the critical exponent

Preservation and positivity of f imply T_2(x) in K for a.e. x in Q. If T_2 is continuous, a value outside the closed K would persist on a nonempty open set of positive nu-mass, impossible. Its connected image lies in a single K_j. If j is outer, its incoming central mass 1/3 exceeds that target's total mass 1/6, also impossible. Thus its central label is one and Delta>=kappa/3.

If T_2 is W^{1,1}_loc, each bounded Lipschitz label is a W^{1,1}_loc characteristic function. The product rule applied to chi^2=chi gives (2chi-1)grad chi=0, hence grad chi=0 a.e. Connectedness makes each label constant. The same mass contradiction forces the central label.

For finite fractional seminorm with alpha=tp>=1, a characteristic label has finite first-difference integral with kernel |x-y|^(-d-alpha). Since Q is bounded, it also has finite such integral at exponent 1. For Q' compactly inside Q and small epsilon, cancellation of the derivative of the mollifier gives

    ||grad(eta_epsilon*chi)||_{L^1(Q')}
      <= C integral_{|z|<epsilon} integral_{Q'}
          |chi(x-z)-chi(x)|/|z|^(d+1) dx dz -> 0.

The limit is absolute continuity of an integrable nonnegative function, not a uniform O(1) estimate. Mollifications converge locally in L^1, so the distributional gradient of chi is zero. This proves constancy at alpha=1 as well as above it. No embedding requiring tp>d, or finite-perimeter assumption on the label, is being substituted. The claimed fixed gap follows.

Conversely, the recovery maps have separated target values on the two sides of each central half-interface. On any relatively interior patch these yield a positive jump and the normal-coordinate integral integral_0^epsilon r^(-alpha) dr, which diverges for alpha>=1. Neither endpoint flattening nor a fractal choice of another label evades the general rigidity proof.

## 7. Constrained infima and attempted counterexamples

For each stated complexity Cmp, the proved lower bound applies to every admissible pair. The constructed pair lies in every relevant admissible class with Cmp<=C_1 n, respectively Cmp<=C_1 n^alpha, and cost excess <=C_2 n^(-2). For a large budget B, choose n=floor(B/C_1) or floor((B/C_1)^(1/alpha)). These are positive and of the required order; they actually meet the budget. This proves two-sided bounds for the infima, even without existence of minimizers. Restricting to preserving order-three maps retains the same upper construction and universal lower bound. Adding the uniformly bounded L^p terms likewise does not change large-budget powers.

For a seminorm budget rather than its pth power, replace B by B^p, giving the exponent 2/t. Optimizing the corresponding lower and upper expressions gives epsilon^(2/3) for Delta+epsilon V and epsilon^(2/(2+alpha)) for Delta+epsilon S as epsilon decreases to zero. These are only infimum estimates. Combining the upper cost with the lower inequalities also forces V_Q(T_n,T_n^2)>=c n and S_Q(T_n,T_n^2)>=c n^alpha for sufficiently large n.

I specifically tried the following failure mechanisms. None contradicts the theorem at its stated scope:

- Concentrating labels in the flat-density boundary layer: the selected branch still has nu-mass at least 1/8, while the mollifier error needs only ||f||_infinity.
- Using outer incoming mass to defeat domination: this only increases target preimage mass and strengthens the inequality.
- Applying the source Hessian with the wrong fixed coordinate: the separate inverse-Lipschitz argument above repairs precisely that potential mistake and is already present in I220.
- Exploding endpoint quantile derivatives: monotone variation, bounded traces, and fixed geometry give the required estimates without a Lipschitz bound.
- Ignoring extension or square-version effects: finite-perimeter zero extension and the choice T(0)=0 address both. Arbitrary global representatives outside the support need not have finite unweighted complexity; the upper theorem chooses the specified representatives.
- Exploiting tp=1 through irregular labels: the vanishing local mollified-gradient proof rules this out.
- Claiming budget sharpness from an upper energy bound alone: the explicit integer choices and universal lower inequalities supply both sides for the actual constrained infima.
- Replacing the product bump by an arbitrary smooth bump: this would require transverse control of conditional quantiles and is outside the passed theorem.

## 8. Reading limits, authentication, and restrictions

AGENTS.md and sources/upstream.json were read completely. Both supplied I217/I220 briefs, the full I220 report, analytic proof, and source note were read completely; their files were also read in place. I220's input-authentication.json was read completely to locate the existing source, without opening any other review. The full family-373 extraction was read in three consecutive ranges, 1–260, 261–520, and 521–749. A first full-output attempt on sources/CONTENTS.md was truncated; it was not a full reading. Only its visible material and the subsequently targeted lines 8988–9010 were read; only family 373 was used.

The sole external comparison independently read for this review was the existing Carioni et al. excerpt: lines 496–561 (including Example 2.8) and 678–859 (complete Example 4.6 and proof), plus the displayed matches of a source-local lookup for Example 4.6/epsilon. The rest of that excerpt and the rest of its original manuscript were not read. Other literature mentioned in I220's source note was not independently read in I222 and is not a proof dependency. The bounded literature note is separate from this verdict.

The input manifest records full-file SHA256 values, byte/line counts, and these reading limits. Hashing a file does not claim full reading. All source copies were reused in place; no new retained source copy was written. Output hashes are returned detached after final writes, with no self-hash or seal in any output.

Only the three assigned I222 files were written. No research code, tests, numerical experiments, repository scans, snapshots, seals, historical replay, shared/ancestor edits, staging, commits, or publication were performed. Ordinary source retrieval, extraction, source-local text lookup, and hashing were used. No subordinate agents were created. Runtime identifies GPT-6.1 Sol with high reasoning effort; an ultrafast service tier is not independently exposed or certified here. This PASS leaves contribution and the final parent acceptance decision open.
