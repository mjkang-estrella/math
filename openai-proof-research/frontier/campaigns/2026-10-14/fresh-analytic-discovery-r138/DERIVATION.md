# Analytic r138 — fixed geometry and harmonic spectral flags

PREFREEZE working derivation; no nominee or frozen theorem. The full question is inherited H from I130/I133, not a new claim or regraded old supporting lemma. Source theorem and proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## Exact retained question

For every fixed 4/9<v<1 and 1<c<9v/4, construct ONE complete smooth metric g on R3, Euclidean near the origin, with Ric_g>=0, normalized asymptotic volume ratio v, and integers k_j tending to infinity such that h_{k_j}(g)>=c(k_j+1)^2. H_k contains real entire harmonic functions satisfying |u(x)|<=C_u(1+d_g(0,x))^k for every x, with an individual finite constant. No unique tangent cone is required. Finite prefixes, per-degree metrics, quasimodes, average/subsequence growth, a different ambient dimension, or loss of normalized independence do not answer H.

## Paid input and proposed stronger composition

The September26 source constructs finite spectral cycles, whole-ball inward contractions, exact finite low invariant graphs, signed scalar crossing matches, and entire harmonic functions with all-radius growth. I130 composes disjoint finite bands; I133 supplies countable geometric slowing and demonstrates failure of uncontrolled normalized exhaustion even with a uniform volume tail. These operations are credited antecedents.

An infinite global column matrix close to the identity is not the only possible composition. Explore an increasing nested FLAG of exact finite-dimensional low spaces. At each fixed cutoff p_i, build its invariant graph over the first p_i reference modes after its activation time. If these graphs are compatible under enlargement, match the finitely many lines only in the quotient by the previous low space. This avoids assuming a bounded inverse for a single countably infinite column matrix. A finite-dimensional upper-triangular lift may preserve the desired degree because all lower ranks have growth well below the newly introduced k_i. This is a proposed reduction; compatibility and simultaneous controls still require proof.

## Scheduling calculation to develop

For each finite program n containing bands i<=n, the rank-cycling identity gives every label of band i a mean q_i<k_i, uniformly over the time allotted to individual loops in the common phase. Those strict margins might finance the positive prefix cost of switching to a more slowly run larger program. Repeating stage n can make its terminal growth deficit arbitrarily negative, while its incomplete-cycle excursion is bounded for that fixed stage. A look-ahead schedule can reserve the next stage's finite excursion before switching. This concerns prescribed rates; exact PDE trace growth and error accumulation must still be connected to it.

## Important distinction

The source p-dependent inverse is not an impossibility theorem: finite activation times may depend on p. Conversely, selecting a late time independently for every p does not establish one consistent harmonic flag or a common family of crossing controls. The actual remaining operation must be tested after this quotient/flag and margin-scheduling reduction.

## Improved finite-quotient reduction

Choose the inherited disjoint bands I_i=(q_i,p_i], q_i=(L_i+1)^2, p_i=(M_i+1)^2. For a fixed i, it suffices to build two exact low trace spaces S_{q_i}(j) subset S_{p_i}(j), both invariant under whole-ball restrictions. An infinite invertible matrix of all columns is unnecessary. Build their graphs by inward iteration from the ordered low spaces at a common terminal radius. Inclusion holds at every finite terminal radius and passes to the two graph limits. This is a compatibility proof conditional on existence of the two controlled limits, not an assertion that independent graph choices automatically agree.

In p_i low coordinates let the smaller exact space be {(x,W_j x)}. If A_j is the p_i-dimensional outward matrix, changing basis by S_j=[[I,0],[W_j,I]] gives an upper triangular block form. Its quotient block is exactly

    B_j=A_BB(j)-W_{j+1} A_LB(j).

The reference matrix is diagonal and both W and the off-diagonal block A_LB are O(delta) whenever the local graph bounds hold. Hence the correction is O(delta^2), preserving the leading signed crossing coefficient within band I_i. This improves on treating all cross-band columns in one infinite array.

If z_{j+1}=B_j z_j is a quotient solution with ||z_j||<=C exp(gamma j), lift with x_{J_i}=0 and

    x_{j+1}=L_j x_j+R_j z_j.

Assume ||L_j||<=exp(beta), beta<gamma, and ||R_j||<=K. Iteration gives

    ||x_j|| <= KC exp(gamma(j-1)) sum_{m>=0} exp((beta-gamma)m).

Thus the lift has the same exponential bound. Here the lower cutoff q_i is of order k_i, its round degree L_i is of order sqrt(k_i), and uniform near-round form comparison bounds beta by O(sqrt(k_i))+O(1), below k_i. This is a finite triangular recurrence, not a new PDE existence assumption once the exact spaces are supplied.

## Nonperiodic graphs: a concrete sufficient criterion

At each fixed rank d consider graph transforms F_j on a fixed closed operator ball of radius r. If

    Lip(F_j)<=1-a_j,   ||F_j(0)||<=a_j r,
    0<a_j<1,          sum_{j>=J} a_j=infinity,

they preserve the ball. Two terminal choices at N change the graph at j by at most 2r product_{l=j}^{N-1}(1-a_l), which tends to zero. Inward terminal iterates are therefore Cauchy at each j, uniformly over controls. The limits are continuous in product controls when finite iterates are continuous, because the tail estimate is uniform. No uniform positive lower bound on a_j is required.

For a local future window of length L on which a_j>=a>0 and ||F_j(0)||<=C delta_j with delta_{j+m}<=2delta_j, the exact limit satisfies

    ||V_j||<=2C delta_j/a + r exp(-aL).

Taking L=(K/a)log(1/delta_j) makes the terminal term arbitrarily smaller than delta_j. This exhibits the precise local-to-infinite-tail estimate needed for the source signed coefficient, rather than invoking a changing-cutoff inverse with no bound.

What still must be integrated is a single angular/radial schedule for which these inequalities, the local frame residuals, and all scalar mismatch endpoint signs hold for every active cutoff and every control choice. The period lengths, gaps and crossing slopes can vary by stage; none is assumed uniform in the band index.

## Prefreeze schedule feasibility

The reference stage n can contain the entire finite disjoint-band program through band n. Its base need only be simple through p_n+1. Connect stage n to stage n+1 by a path simple through p_n+1; introduce the new cutoffs only after a constant collar at the new base. Thus a new cutoff never has to be defined across old high-spectrum degeneracies. All previously active cutoff gaps remain positive on the connector. Each stage is run for an integer number of full label periods, so old labels arrive at the connector in their original ordered ranks.

Use one phase speed eta(t)=t^(-3/4) on the unwrapped concatenation; do not choose an independent constant speed at every stage. For each finite stage and each adjacent-stage connector, all finitely many active gaps, slopes, frame norms, variation directions and phase lengths are finite data. Repeating the preceding stage postpones the next connector until any prescribed finite time threshold. Curvature cost is bounded by C_n integral_{T_n}^infinity t^(-3/2)dt=2C_n/sqrt(T_n), independent of how many periods stage n runs. This avoids the circular constant-speed budget in which banking for a slower next stage exhausts the previous stage's curvature allowance.

For a mean-zero phase rate with primitive bounded by A_{i,n}, integration by parts gives a prefix discrepancy at most C A_{i,n} t^(3/4) on a stage beginning at T_n. Requiring C A_{i,n} T_n^(-1/4)<=2^(-n) for all i<=n bounds this by 2^(-n)t at EVERY prefix. Connectors have finite phase lengths and rates bounded by the fixed band rank, so their entire contributions obey the same bound after postponement. A fixed finite initial collection of stages contributes a fixed constant; the sum over n>=N is <=2^(1-N)t. The total error is o(t), while each band's mean upper bound q_i<k_i stays fixed.

For exact graphs first impose only the ball-preservation and contraction inequalities above, at both cutoffs of every active band. The local reference gap yields a strictly positive contraction deficit on each compact stage/connector, although this minimum can tend to zero with n. Delay each stage until its frame/operator errors are smaller than that deficit times the chosen graph radius. Run at least one full period sufficiently late that the sum of deficits on that period exceeds one. Consequently the infinite product of contraction factors vanishes for every fixed active cutoff. This creates the exact graphs and their product-control continuity before any signed-coefficient estimate uses them.

Next localize the graph to a future window K_n log(t), choosing K_n after that finite neighborhood's minimum gap. The controlled terminal graph is already bounded. Its contribution is <=r exp(-a_n K_n log t); the local inhomogeneous terms give O(C_n delta(t)). Source finite-frame freezing uses a backward window 4log(1/eta). Both windows are negligible compared with a fixed phase collar's length, which is comparable to t^(3/4). At joins they lie in the union of the two finite neighboring programs and their connector. All constants remain finite before choosing the join time. This supplies the source O(delta) graph bound and o(delta) crossing remainder locally, uniformly over the entire future control product, without asserting a cutoff-uniform norm estimate.

Every pair of labels inside a band crosses during every full label period. Hence each scalar matching interval is finite; the only infinite-tail dependence is already inside the continuous exact graphs. A matching interval touching a stage boundary contains at most the last full old period, the connector and the first full new period. Once those two programs are chosen, its phase lengths and gap profile are finite. The same Gaussian central window and exponentially suppressed outside-plateau estimate therefore apply after that boundary is delayed. Coordinate forces involve only the finite quotient band. These are the constraints that need an explicit proof in the author development, not an invocation of the fixed-p theorem with p=infinity.

The feasibility route now consists of (i) common slow scheduling with summable curvature and o(t) prefix errors, (ii) fixed-rank nonuniformly contracting graph limits at two cutoffs per band, (iii) nested-graph quotient matching in a countable product of finite rows, and (iv) triangular lifts and whole-ball extension. No uniform-in-i constants or infinite column inverse enter. Full scope is retained for proof development; later defects, if found, must leave the scope unchanged.
