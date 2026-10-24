# r219 working mathematical derivations (prefreeze)

Authority: Codex / GPT-6 Astra / xhigh / default service tier, per the current user header. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all its operative proofs are assumed true. No correctness, contribution, acceptance, or count is assigned here. These are research calculations; no full-scope nominee has been frozen.

## 1. Paid interfaces actually read

Source343 uses capacity c=pi|z|^2, volume c^n/n!, n>=3, closed sources with neighborhood embeddings, open target. All seven operative sections were read completely, in driver order, as well as both figure sources and the bibliography. `app:large` and `six:large` actually put the smaller balls in the standard open shell a<pi|z|^2<1, with a larger than the requested central capacity. Their shell avoidance is stronger than the finite theorem statement. `geo:shell`, relative Kahler Moser, normal-cone transfer, the six-dimensional lower cut, and exactly normalized moment transfer are all paid, with their stated hypotheses. No arbitrary prescribed embedding can be identified with that central ball merely by cohomology.

Original eligible I70 mathematical sections specify the arbitrary-prefix relative target RP and prove isotopy extension, the centered-shell case, orbit-average identities, bracket countermodels, and small-ball filling with fixed volume slack. Original I74 mathematical sections construct shear and derivative-controlled paths and a protected comparison/suspension. None of these targets is reopened. No old disposition is a premise. The countable source topology considered below is absent from the I70 target as actually read.

## 2. Finite-to-countable proper packing: shell schedule

Let (c_i) be positive and S=sum_i c_i^n<R^n, with c_i+c_j<R for i!=j. The sequence tends to zero. Its two largest terms exist (for an infinite positive summable sequence), so p=max_{i!=j}(c_i+c_j)<R. Choose A with max(S^(1/n),p,R/2)<A<R. Every finite prefix satisfies the finite packing criterion in B(A). This uniform A is chosen before any tail grouping.

Select a prefix N so that its remaining total T_N=sum_{i>N}c_i^n and largest remaining capacity delta_N are arbitrarily small. Put tail band j in (delta_N*2^(-j-1),delta_N*2^(-j)], j>=0; every band is finite. Let V_j be its capacity-power sum. Provisional shell widths

    w_j=delta_N*2^(-j) + V_j/(n*A^(n-1)) + epsilon*2^(-j-1)

have sum 2*delta_N+T_N/(n*A^(n-1))+epsilon, which is less than R-A for sufficiently late N and small epsilon. Add a positive geometric allocation of the unused width so that the final widths d_j sum exactly R-A. Set A_0=A, A_(j+1)=A_j+d_j. Then A_j increases to R, every ball of band j has c_i<d_j, and

    A_(j+1)^n-A_j^n >= n*A^(n-1)*d_j > V_j.

The paid shell construction applies after normalization to the central capacity A_j/A_(j+1)>1/2, the latter because A>R/2. Also d_j<A_j, so two tail capacities have sum <2*d_j<A_(j+1); this checks the pair hypotheses of the six-dimensional proposition as well. Strictness permits the finite auxiliary inflations used in both source proofs. It puts the entire band compactly in A_j<pi|z|^2<A_(j+1), with neighborhood extensions. No previously chosen map changes. Empty bands cause no problem. Each compact subset of the open target lies below some A_j, so it meets only finitely many bands and hence finitely many images. Neighborhoods can be shrunk within the individual shells and within finite-band separation. This proves a proper embedding of the topological sum of the closed balls, with pairwise disjoint open neighborhood images. Smoothness and symplecticity are componentwise, not inferred from a limit of derivatives.

The above is a complete feasibility calculation, not a substantiality claim. An even simpler compatible reduction follows.

## 3. Elementary carrier reduction: the shell construction is unnecessary

Let q=R^(1/2)/sqrt(pi), q_A=A^(1/2)/sqrt(pi). Fix any chosen boundary point x of the radius-q Euclidean ball, write e=x/q, and choose 0<h<q-q_A. Given a sufficiently late prefix N_0, choose strictly increasing N_j so that

    T_(N_(j-1)) <= epsilon*16^(-n*(j-1)), j>=1.

This is possible by choosing N_0 with T_(N_0)<=epsilon, then each N_j with T_(N_j)<=epsilon*16^(-n*j). Each finite block I_j=(N_(j-1),N_j] has volume budget <=t_j=epsilon*16^(-n*(j-1)). Set carrier capacity C_j=3*t_j^(1/n). For each block,

    sum_(i in I_j)c_i^n <= t_j < C_j^n,
    c_i+c_l <= 2*t_j^(1/n) < C_j.

Thus the finite theorem places the block in a carrier ball of capacity C_j. Its Euclidean radius is d_j=sqrt(3/pi)*epsilon^(1/(2n))*4^(-(j-1)). The sum D=sum d_j=(4/3)*sqrt(3/pi)*epsilon^(1/(2n)) can be made smaller than h/6.

Put s_j=3*sum_(l>=j)d_l and center y_j=(q-s_j)e. Carrier j is the Euclidean ball of radius d_j about y_j. Its distance to the boundary point tends to zero. It is strictly in the open target since s_j>d_j. It misses the central B(A), since s_j+d_j<=4D<h<q-q_A. For j<k,

    |y_j-y_k|=3*sum_(l=j)^(k-1)d_l >=3*d_j>d_j+d_k.

All carriers are strictly disjoint, and their radii and distances to x tend to zero. Every compact subset of the open target misses all sufficiently late carriers. A finite prefix packing in B(A), followed by independently chosen finite block packings and Euclidean translations into these carriers, therefore yields the same proper countable packing with pairwise disjoint neighborhood images. The only accumulation point in the closed ambient ball is x.

This executes the strongest simpler alternative: no infinite Moser path, shell isotopy, derivative compactness, or compatible extension of previously moved balls is required. The finite-to-countable passage consists of a summable-radius carrier schedule and finite disjoint-union assembly. It cannot be advertised as an unpaid version of the difficult source shell construction.

## 4. Strict volume and topology: an infinite-source trap

A locally finite family of disjoint compact images has closed union relative to the open target. This union cannot equal the connected open target: if it has at least two components, each is relatively open in the union by local finiteness and finite separation. For a single component compactness already rules out equality. Its nonempty complement is therefore open and has positive volume. Countable additivity gives sum_i c_i^n<R^n. Each pair separately has strict pairwise inequality by compact containment and the two-ball obstruction.

There is a stronger reason for strict volume when the neighborhood images are required to be pairwise disjoint, even without local finiteness. Fix one component. Its embedding on a neighborhood includes a nonempty open collar outside that component's closed image. The collar is disjoint from all other components' closed images, because their neighborhoods are disjoint. This collar alone gives a positive volume deficit. Hence volume equality cannot occur in this category.

Even a topological embedding of the topological sum of closed balls implies isolation of each component in the union. The component is open in the topological sum, so it is the intersection of the total image with an ambient open set. Compactness and its individual neighborhood extension then produce a positive-volume collar avoiding all other closed images. Thus a full-measure collection with accumulation on component boundaries, if such a collection exists, must be understood as individual component maps with an injective set-map whose inverse need not be continuous in the disjoint-sum topology. It would not be the proper/countable-neighborhood packing considered here. No equality theorem is inferred by rescaling.

## 5. Prescribed boundary accumulation set: closing the feasibility variant

The initial feasibility note used a forward choice of carriers that risked circular dependence on the preceding tail cutoff. The following fixed radial schedule removes that issue completely, before any nominee freeze.

Let K be a nonempty closed subset of the radius-q sphere. Choose a sequence x_j in K whose subsequential limit set is exactly K: concatenate finite 1/m-nets of K, repeating points if necessary. All points lie in the compact K, and every point of K is approached by an infinite subsequence. Fix 0<h<q-q_A, set s_j=h*2^(-j), d_j=s_j/8, and C_j=pi*d_j^2. Put

    t_j=(C_j/3)^n.

Choose N_0>=1 with T_(N_0)<=t_1, and then strictly increasing N_j with T_(N_j)<=t_(j+1). This is possible for every j because the tails tend to zero; it also ensures N_j tends to infinity and every block I_j is nonempty. For a block I_j, its total capacity-power is <=t_j, and each capacity is <=t_j^(1/n). Thus its pair sums are <=2*C_j/3<C_j and its total is <=C_j^n/3^n<C_j^n. Apply the finite theorem to that finite block inside a carrier of capacity C_j.

Translate carrier j to center y_j=(1-s_j/q)*x_j. Every point of it has norm between q-s_j-d_j and q-s_j+d_j. It is inside the target, outside B(A), and the radial intervals are disjoint. In fact for k>j,

    s_j-s_k >= s_j/2,
    d_j+d_k <= 3*s_j/16 < s_j/2.

The reverse triangle inequality proves separation of carriers regardless of their directions. Radial containment also proves local finiteness in the target. Any sequence of points from distinct tail images lies within s_j+d_j of x_j, so all its limits are in K. Conversely pick any point from each nonempty block; along a subsequence x_j tending to x in K these selected points also tend to x. Consequently the accumulation set of the *family* of closed images in the closed ambient ball is precisely K. This means limits drawn from infinitely many distinct components, not the ordinary derived set of their union. No accumulation occurs in the open target or on an earlier compact image.

This closes the proposed boundary-set variant, but its operations remain elementary tail scheduling, finite source packing, and translation. It is retained as a derivation, not offered as a nonroutine nomination.

## 6. What has not been obtained

No new result on arbitrary fixed prefixes, a global continuous section over capacity space, parametric transitions, a fixed-capacity isotopy class, or an effective derivative estimate follows from these constructions. The old RP target is neither renamed nor narrowed. A full-measure limiting collection changes the category if collars/topological embedding are lost. The elementary carrier reduction must be included in any contribution assessment of the proper countable extension.

## 7. A countable blowup consequence, with the topology and volume carried through

Use the fixed radial carrier construction of section 5 (or the one-point version). Perform the ordinary symplectic point blowup in each disjoint neighborhood of a closed source ball, at capacity c_i. The operation is the exact local interface in Siegel--Yao section 2.1, equation (5), and Source343 `geo:shell`: a punctured neighborhood of the exceptional CP^(n-1) is identified symplectically with the shell c_i<pi|z|^2<c_i+epsilon_i in the actual source coordinates. Choose epsilon_i>0 small enough that the enlarged source embeds and that the resulting neighborhoods remain disjoint in their carriers. There is no requirement of a positive infimum of epsilon_i.

The family is locally finite. Therefore the cut/gluing atlas near any target interior point involves only finitely many pieces. It defines a smooth Hausdorff second-countable 2n-manifold X with a smooth symplectic form, not a formal infinite sum of two-forms. Hausdorffness follows from the ordinary finite blowup charts on each compact subregion and separation from every later carrier. A countable union of these countable local bases supplies second countability. Local nondegeneracy is the finite blowup nondegeneracy. Exceptional divisors are mutually disjoint and locally finite, and a line in the i-th divisor has symplectic area c_i, in the capacity convention of this round.

The complement of the exceptional divisors is symplectomorphic to the complement of the closed packed balls. Each divisor has real codimension two, hence zero ambient symplectic volume. Countable additivity gives

    Vol(X)=(R^n-sum_i c_i^n)/n! > 0.

The countable blowups do not produce a compact manifold with a smooth boundary at infinity. Here is a direct calculation, avoiding an assumption about completing an infinite metric. Take radial spheres between successive carrier bands, beyond the finite central packing. Their bounded interiors contain only finitely many source balls and hence produce an exhaustion X_j by finite blown-up open balls. Every compact subset of X is contained in some X_j, because the blowup modification is confined to locally finite carrier neighborhoods. For a finite blown-up ball, decompose it into the ball with finitely many interior balls removed and the exceptional disk-bundle pieces. Each overlap retracts to S^(2n-1); for n>=3 its H_1 and H_2 vanish. The punctured ball has H_2=0. Each exceptional disk bundle retracts to CP^(n-1), with H_2=Z generated by a line. The Mayer--Vietoris exact sequence therefore gives H_2(X_j;Z)=Z^(number of enclosed balls). The inclusion X_j->X_(j+1) preserves these generators and adjoins the new ones.

Every singular cycle and every singular bounding chain has compact image and lies in one exhaustion member. Consequently homology commutes here with this increasing exhaustion directly at the chain level, and

    H_2(X;Z) = direct_sum_(i>=1) Z[ell_i], where ell_i is a projective line in the i-th exceptional divisor.

A compact smooth manifold has finite CW type, and its interior is homotopy equivalent to it using a boundary collar. Hence X cannot be diffeomorphic to the interior of any compact smooth manifold with boundary. This is a topological obstruction to a smooth compactification of this particular countable blowup, not a new ball-packing obstruction and not a claim about a compactification by a singular boundary or by changing the topology. All infinite smoothness claims were paid by local finiteness, not by uniform derivative or curvature bounds. The consequence is another ordinary composition of the completed countable construction with the classical local blowup and Mayer--Vietoris calculation; it is not nominated.

## 8. Quantitative limitation that does not overclaim

A capacity gap cannot bound the derivatives of *every chosen representative* of a packing. In a Darboux box strictly inside a source ball choose a compactly supported Hamiltonian which equals (epsilon/k)*sin(k*q_1) on a smaller box. On a still smaller box whose trajectory stays inside, the time-one map is the shear p_1 -> p_1 plus or minus epsilon*cos(k*q_1), with sign set by the Hamiltonian convention. Take epsilon small enough for this local trace. The cutoff keeps the global flow supported in the interior of the ball, so it maps the whole ball onto itself. Its first derivative contains epsilon*k*sin(k*q_1), unbounded as k increases. Composing a fixed neighborhood embedding with these source symplectomorphisms leaves its compact image, capacity, volume and all inter-image clearances unchanged. On that fixed compact box the derivative of the original embedding is uniformly invertible, so the derivative norms of the compositions are unbounded too.

This supplies no lower bound on the optimal derivative norm among all embeddings and no obstruction to a carefully chosen controlled packing. The construction explicitly distinguishes a statement about all representatives from a quantitative existence theorem. No effective source estimate or new rate has been obtained.

## 9. Timing and scope decision

The first versions of sections 2--4 were feasibility deductions after the complete Source343 proof and eligible original mathematical sections had been read, and after initial primary reads of Siegel--Yao section 7 and Edtmair section 1.1. The full primary comparisons (Siegel--Yao section 2, McDuff--Polterovich, Schlenk, Gromov and Kahler cuts) came later in this prefreeze round; this timing is recorded rather than presented as earlier proof coverage. The strongest elementary carrier alternative does not require importing any unread external theorem. The blowup calculation in section 7 was written after reading its actual primary local interface. No frozen substantial target or full author-proof nominee has been created.
