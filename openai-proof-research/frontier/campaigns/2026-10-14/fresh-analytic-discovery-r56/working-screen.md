# Canonical hard-sphere fluctuations: pre-freeze operation screen

Author: Myeongjin Kang. No affiliation. Original prose CC BY 4.0.

Status: **NO NOMINEE; no theorem scope frozen.** This is author-side research, not an independent gate. The full canonical question below remains unproved here and is not refuted. The initial operations and limiting covariance adaptation look technical in light of the actual primary operations; the remaining source-level estimates are identified rather than silently assumed. No count is requested.

## The full question examined

In dimension three, let f0 be a nonnegative smooth probability density satisfying the spatially summable Gaussian density and spatial-gradient hypotheses of source H, and let [0,T] be any finite regular interval supplied by H's classical Boltzmann hypothesis. For each integer N, set epsilon=N^(-1/2). Put the canonical initial law on N labeled particles proportional to

    1_{all |x_i-x_j|>epsilon} product_i f0(z_i) dz_i,

and evolve the actual elastic hard-sphere flow on R3. The prospective assertion is convergence of every fixed finite list of real smooth compactly supported test observations at arbitrary fixed times in [0,T], normalized by N^(-1/2) and centered at their EXACT CANONICAL microscopic expectations, to the fluctuating Boltzmann Gaussian with the source's drift/noise and initial covariance

    integral f0 phi psi - (integral f0 phi)(integral f0 psi).

No small-time, equilibrium, extra spatial compactness, or trajectory smoothing restriction is imposed. This paragraph records the unchanged full question explored, not a frozen candidate or proof. No functional path-space result is substituted. The prior accepted kinetic path theorem is explicitly grand canonical.

## 1. Activity and mean are different at fluctuation scale

Source H has activity mu=epsilon^(-2). Its initial rooted Mayer calculation gives uniformly

    g0(z)=f0(z)[1-mu integral_{|x-x*|<=epsilon} rho0(x*) dx*+O(epsilon^2)].

Because rho0 and its gradient are bounded and integral f0=1, this can be integrated against the bounded test 1, even though the displayed smooth-test centering-shift statement is narrower. Consequently

    (E N-mu)/sqrt(mu) -> -c0,
    c0=(4pi/3) integral rho0(x)^2 dx > 0.

The uniform remainder, multiplied by integral f0, is O(epsilon^2); the ball-average error is O(epsilon^4) before multiplication by mu. Thus the assertion for test 1 does not require an unproved extension by weak convergence.

For N=mu an integer, conditioning fixes the grand-canonical *exact-centered* mass fluctuation at a value tending to c0, not zero. An activity factor mu^N/N! cancels under this conditioning, so its conditional law is exactly the canonical law displayed above. Exact conditional recentering is essential: merely deleting the mass covariance from a grand-canonical centered Gaussian would otherwise miss a possible conditional mean. This is not a proof of a conditioned Gaussian limit.

Write U(0,t) for H's backward linearized propagator. If the canonical limit holds, its covariance differs from the grand-canonical covariance by

    -b_t(phi)b_s(psi),   b_t(phi)=integral f0 U(0,t)phi.

Indeed the conserved mass mode has variance one and covariance b_t(phi) with a t-observation. This is a statement about the Gaussian model: conditional covariance is the Schur complement, and exact recentering removes the Gaussian conditional mean. In a nonequilibrium nonlinear problem, one must NOT replace b_t(phi) without proof by integral f_t phi. H's Section 07 covariance propagation directly supports the U formula.

Parent author assistance first highlighted the activity/mean scaling issue. The explicit three-dimensional coefficient above was then checked from H's actual uniform expansion. No independent-review credit is claimed.

## 2. Why a joint central limit theorem does not condition itself

Here is an exact counterexample to that inference, not a hard-sphere counterexample. Let K_n be Poisson(n), let G be an independent standard Gaussian, and put Y_n=(-1)^(K_n)|G|. The joint law of ((K_n-n)/sqrt(n),Y_n) tends to two independent standard Gaussians. To see this, the parity-weighted characteristic factor equals

    E[(-1)^K exp(iu(K-n)/sqrt(n))]
      =exp(-iu sqrt(n)+n[-exp(iu/sqrt(n))-1]),

whose modulus is exp(-n[1+cos(u/sqrt(n))]) -> 0. The unweighted factor tends to exp(-u^2/2), and the two half-normal characteristic functions average to the normal one. Yet conditioning K_n=n makes Y_n a signed half-normal. After exact conditional centering it remains non-Gaussian, with variance 1-2/pi. Thus even the jointly Gaussian unconditioned limit and exact conditional centering do not suffice. No conclusion about the gas is drawn from this example.

H's fixed-order estimates also do not, by themselves, supply an all-order analytic generating function or a joint lattice local limit theorem. The coarse rare-event transfer is insufficient on its own: if the count event has probability of order epsilon, conditioning H's O(epsilon^(1+eta)) exceptional event gives only O(epsilon^eta). Multiplying by sqrt(N)=epsilon^-1 to compare exact means is not small when eta=1/20. This calculation is conditional on that local probability estimate and is an insufficiency of this crude bound only. Direct canonical estimates can avoid the loss.

## 3. Direct canonical factorial control is elementary

Let b=||rho0||infinity vol(B_epsilon), and let Z_k be the k-particle product-exclusion integral, with Z_0=1. If Nb<1, sequential insertion and the union bound give

    1-(k-1)b <= Z_k/Z_(k-1) <= 1  (1<=k<=N).

Thus every Z_k is positive. The normalized canonical factorial density, extended by zero for h>N, is

    F_h^N(Z_h)=(N)_h/N^h * 1_Dh product_i f0(z_i)
                 * Z_(N-h)[Z_h]/Z_N.

The bracketed partition function additionally avoids all h fixed balls, so Z_(N-h)[Z_h]<=Z_(N-h). It follows that

    0<=F_h^N<= (1-Nb)^(-h) product_i f0(z_i).

For Nb<=1/2 this is at most exp(2Nbh) product_i f0. It is an all-h statement, and is uniform also for slowly growing h; Nb=O(epsilon). The falling factorial only improves the upper bound.

For the one-point lower bound, under the (N-1)-particle canonical law the density of any labeled particle is at most f0/(1-Nb), by the same upper bound. The probability that any one of these particles lies in a specified epsilon-ball is therefore at most (N-1)b/(1-Nb). Since Z_(N-1)/Z_N>=1, insertion yields

    F_1^N >= [1-(N-1)b/(1-Nb)] f0 >= (1-2Nb)f0

when Nb<=1/2. Together with the upper bound this proves the source-norm O(epsilon) one-point approximation. These estimates do not prove the connected-cumulant contract needed for the full dynamics. They do show that conditioning an exceptional event is unnecessary for elementary positive initial bounds.

## 4. Where the new initial term goes: a finite counting lemma

The following is an algebraic graph lemma, not a completed rederivation of H's expansion. Suppose a retained rooted forest term has h designated roots, m particle lines, and c physical components, each containing a designated root. Thus c<=h. Suppose physical merger integrations contribute mu^(-(m-c)), particle summations contribute mu^(m-h), and p nonlocal initial connections contribute mu^(-p), with enough connections to connect the c components. Its total power is

    mu^(c-h-p).

Connectivity implies p>=c-1. A leading term of order mu^(1-h) therefore has exactly p=c-1<=h-1; the intercomponent connections form a tree. Each additional initial connection costs at least mu^-1. For an initial block joining k components, count k-1 independent connections; the same argument applies after replacing it by a spanning tree. This bookkeeping does not justify a bound on its coefficients or spatial traces.

In particular the proposed canonical correction does not force arbitrarily many leading nonlocal connectors at a fixed observed order. At h=1 no such connector survives; at h=2 a single connector can propagate the initial rank-one covariance. This is exactly the type of linearized transport of initial correlations described by BGSS Section 1.6. It removes one apparent complexity objection but supplies no new collision geometry.

For ideal independent fixed-N particles, the normalized factorial generating functional is

    E product_i(1+u(z_i)) = (1+integral f0 u)^N.

Taking its logarithm shows the normalized factorial cumulant of order h is exactly

    (-1)^(h-1)(h-1)! N^(1-h) f0^tensor h.

In particular its second cumulant is -N^-1 f0 tensor f0, even at separated points. Thus H's grand-canonical sharp initial-link bound, whose links are short-range indicators plus arbitrarily small epsilon^D tails, cannot be imported unchanged for canonical data. The global 1/N connectors must be included explicitly. The full hard-core initial asymptotics are NOT claimed proved by this ideal-gas calculation.

## 5. Actual primary operations and the remaining contract

BGSS, arXiv:2008.10403v2, Theorem 2, proves the grand-canonical short-time Gaussian theorem. Its Section 1.6 explicitly describes both linearized transport of general initial correlations and the fixed-N long-range 1/N covariance term. This is a substantive antecedent, not a title-only resemblance.

Pulvirenti--Tsagkarogiannis, arXiv:1409.2718v3, Sections 3.1 and 7, writes the canonical partition function as an abstract polymer model and introduces marked activities to obtain one- and two-point correlations. Equations (7.5)--(7.9) give the marked polymer identity and convergence bound; the remainder of Section 7 proves Theorem 2.5 by selecting the two marked coefficients and bounding their clusters. The paper's spatial model is a bounded box with uniform base measure and stable finite-range interaction. Its printed theorem is not an all-order whole-space inhomogeneous dynamic theorem.

Replacing the uniform base measure by f0(z)dz makes a physical tree integration cost b per leaf, with Nb=O(epsilon), and the same canonical polymer organization is the natural initial calculation. Formally, for bounded u and m(u)=integral f0(1+u), the exact identity is

    E_QN product_i(1+u(z_i))
       = m(u)^N Z_N(f0(1+u)/m(u))/Z_N(f0).

The first logarithmic term is the ideal fixed-N cumulant above. The second is a standard canonical interaction polymer sum. A scalar analytic bound on this expression is not automatically a total-variation, pointwise trace, or polylogarithmic-order hierarchy estimate; those norms have to be proved in the relevant marked polymer space.

H's one-slab factorial identity (Section 04, Lemma one-slab-expansion, eq. one-slab-exact) is explicitly valid for an arbitrary positive input law. Therefore changing the ensemble does not require a new deterministic collision identity. The unfinished full proof would need (i) canonical marked initial bounds including the nonlocal connectors, uniformly in the orders used by H's cutoffs; (ii) the sharp local/spatial-trace estimates when these connectors join physical components; (iii) full retained-tree remainders and canonical true-flow exceptional-event estimates; and (iv) passage through H's last-contact covariance evolution. Section 4 above addresses only the finite leading-power count. None of (i)--(iii) is silently licensed by a two-point primary theorem or a fixed-order total-variation guess.

The operation comparison gives no credible substantial candidate at present: the new ensemble's canonical clusters and its extra covariance transport are already identified in the actual primary literature, while H supplies the long-time deterministic expansion and Gaussian evolution. A complete careful adaptation may be useful, but length of that adaptation would not establish substantiality. Conversely this assessment is not a claim that the whole prospective theorem follows verbatim from a cited theorem. It remains unproved in this packet, with the precise contract above outstanding.
