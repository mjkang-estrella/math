# CM275: QMA membership for the full unit-charge Coulomb problem

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. This is an author proof submitted for independent proof and contribution review, not an independent verdict. The exact scope is frozen in original-scope.md. The stipulated upstream hardness theorem is used only in the final completeness conclusion.

## 1. Statement, input and constants

For every input in original-scope.md, the full spinful antisymmetric Coulomb spectral-infimum decision problem belongs to QMA. Consequently it is QMA-complete under classical deterministic polynomial-time many-one reductions, using the stipulated unit-charge source Theorem 1.

Write

    T = (1/2) sum_i ||grad_i psi||_2^2,
    C = 4 N M^2,  g = b-a,  eta = min(1,g/100),  D=3N.

All estimates below hold for spinor-valued wave functions, summing over the finite spin indices. In particular none selects a spin sector. Constants chosen below are deliberately generous. N and M are at most the input length L, and eta^(-1)<=100L. An integer with exponentially large value is permitted only when its binary length is polynomial. No step enumerates its range.

We prove a uniform finite-space comparison, then implement a verifier. The finite space has exponentially many one-particle modes but only polynomially many encoding qubits. Membership does not assert efficient preparation of a ground state: the witness is supplied by Merlin.

## 2. Form estimates uniform in the nuclear positions

Three-dimensional Hardy, applied to x_i with all other coordinates fixed, gives

    integral |psi|^2/|x_i-y|^2 <= 4 ||grad_i psi||_2^2.

Here y can be a fixed nucleus or another particle coordinate. Integrating the other coordinates and summing spin indices preserves the inequality. Cauchy–Schwarz therefore gives, for normalized psi,

    sum_{i,alpha} integral |psi|^2/|x_i-R_alpha|
       <= 2 M sum_i ||grad_i psi||_2
       <= 2 sqrt(2) M sqrt(N) sqrt(T)
       <= T/2 + C.

Repulsion is nonnegative. Thus the full Coulomb form q satisfies

    q >= T/2-C.                                                (2.1)

The same estimate holds on any Dirichlet open subset by zero extension. The usual epsilon version of Young's inequality gives infinitesimal form bounds for all finitely many Coulomb terms; hence these forms are closed and lower bounded on their stated H1 domains. We use their associated self-adjoint operators and variational infima. This also follows from the stipulated source's form convention, but the numerical estimate is shown here.

Let E be the full-space infimum. Then -C<=E<=0. For the upper bound choose N normalized smooth packets with common length scale R, mutually separated by distance at least R^2, and antisymmetrize their product with any fixed spin choices. Their disjoint supports give a normalized wedge, kinetic energy O(N/R^2), repulsion O(N^2/R^2), and nonpositive attraction. Let R tend to infinity. No eigenvector attainment is used.

For epsilon>0 define v_epsilon(r)=min(r^(-1),epsilon^(-1)), including v_epsilon(0)=epsilon^(-1), and replace every attractive and repulsive Coulomb kernel by v_epsilon. Write q_epsilon for the result. Pointwise,

    0 <= r^(-1)-v_epsilon(r) <= epsilon/r^2.

Applying Hardy to the lower-index coordinate in each pair gives

    |q_epsilon[psi]-q[psi]|
       <= 8 epsilon (M+N) T[psi].                             (2.2)

No minimum inter-nuclear or inter-particle distance occurs in this estimate. Since capped attraction is no greater than original attraction and capped repulsion remains nonnegative, (2.1) also holds for q_epsilon.

## 3. Finite box without a binding promise

Let A=1+max_alpha ||R_alpha||_infinity and R_0=2A; every nucleus lies in the Euclidean ball of radius R_0. Choose an integer

    s >= 100 (NM+N^2+N+1)/eta.

Take a Lipschitz angle theta(r) which is zero for r<=R_0+s, equals pi/2 for r>=R_0+2s, and has |theta'|<=2/s. Put chi_in=cos(theta(|x|)) and chi_out=sin(theta(|x|)). Their squares sum to one, and the sum of their squared gradients is at most 4/s^2. Lipschitz cutoffs suffice for the H1 form identity; smooth approximations give the same bounds if desired.

For each subset S of {1,...,N}, multiply psi by chi_in in the coordinates of S and by chi_out in the other coordinates; call the result psi_S. The product partition has sum_S ||psi_S||^2=||psi||^2. The IMS identity for kinetic normalization 1/2 gives

    q[psi] >= sum_S q[psi_S] - 2N/s^2 ||psi||^2.              (3.1)

Let E_k^ball be the k-particle Coulomb Dirichlet infimum with the same nuclei in the open ball B(0,R_0+2s); set E_0^ball=0. It is finite by (2.1), and its domain is nonempty for every finite k. In a term psi_S, the coordinates indexed by S are antisymmetric among themselves (position and spin together), and are in that Dirichlet form domain. Slicing over the other positions and spins therefore bounds their internal form by E_|S|^ball ||psi_S||^2. This assertion does not require antisymmetry between an inside and an outside coordinate in an individual localized term.

Whenever an outside factor is nonzero, its electron is at distance at least s from each nucleus. Discard all outside kinetic terms and every repulsion involving an outside particle; they are nonnegative. Outside attraction is at least -NM/s. Thus

    q[psi_S] >= (E_|S|^ball-NM/s)||psi_S||^2,

and (3.1), followed by the full-space infimum, implies

    min_{0<=k<=N} E_k^ball <= E + NM/s + 2N/s^2.              (3.2)

This is the step that retains arbitrary escaping electrons.

We next return to N particles in one box. For each k use any normalized near-minimizer for E_k^ball. Add N-k one-particle packets, with mutually disjoint supports, in cubes of side s centered at

    c_j=(R_0+2s+(4j+2)s,0,0),  1<=j<=N-k.

Each packet is the product of the normalized first Dirichlet sine modes of its cube, extended by zero, and may be assigned spin up. Its kinetic energy is 3pi^2/(2s^2)<15/s^2. Its support is at distance at least s from the inner ball and from every other packet's support. Wedge these packets with the k-particle state. The orthogonal spatial-support decomposition of the one-particle Hilbert space makes this wedge isometric: its norm is one. Equivalently expand the antisymmetrization into disjoint coordinate-support assignments; mixed assignments have disjoint support and the normalization factors cancel. That same expansion shows that internal kinetic and potential expectations are preserved, and the added repulsions are bounded by N^2/(2s). Added attraction is nonpositive and can be discarded for an upper bound.

Choose a power-of-two integer B >= R_0+(4N+6)s, with B less than twice the ceiling of that expression. Let Q=(-B,B)^3 and let E_Q be the N-particle Dirichlet infimum on Q, retaining all spin sectors. Every packet and the inner ball fit inside Q. Taking the internal near-minimizer limit, then the minimum over k, gives

    E_Q <= min_k E_k^ball + 15N/s^2 + N^2/(2s).

Together with zero extension and (3.2),

    E <= E_Q <= E + eta.                                     (3.3)

Indeed NM/s+N^2/(2s)+17N/s^2<eta for the displayed choice of s. No algorithm has to identify which k realizes the minimum: the argument proves existence of a good N-particle witness. There is no exponential-physical-diameter promise: log B is O(L+log s+log N), since each nuclear coordinate has at most L bits. Empty inner sectors, ions with N>M, and spectra without a lowest eigenvector are all included.

## 4. Capping and a controlled spectral compression

On Q choose

    epsilon = eta/[128(M+N)(C+2)],
    alpha = 8epsilon(M+N) = eta/[16(C+2)].

Let E_epsilon be the N-particle antisymmetric capped Dirichlet infimum. A normalized near-minimizer for E_Q has T<=2(C+eta+o(1)) by (2.1) and (3.3). Equations (2.2) and (3.3) imply

    -C <= E_epsilon <= E_Q+eta/8 <= 2.

Conversely a normalized near-minimizer for E_epsilon has T<=2(C+2+o(1)). Evaluating its uncapped form gives E_Q<=E_epsilon+eta/8. Hence, safely,

    |E_epsilon-E_Q| <= eta/4.                                (4.1)

Set

    B_V = N(M+N)/epsilon,
    G = 2N(M+N)/epsilon^2,
    J = C+2+B_V.

The capped multiplication potential has norm at most B_V and Lipschitz constant at most G in the Euclidean metric on all D spatial coordinates. Each one-particle kernel has Lipschitz constant epsilon^(-2), each pair kernel at most sqrt(2)epsilon^(-2); summing proves the bound. Nuclear clustering causes no increase in these constants beyond M.

The Dirichlet kinetic operator T_Q on the finite cube has compact resolvent. The bounded real potential preserves its operator domain and compact resolvent. Restricting to the closed antisymmetric subspace preserves these facts: permutation operators commute with both terms. Thus a normalized eigenvector psi for E_epsilon exists in Dom(T_Q), and

    ||T_Q psi|| <= |E_epsilon|+B_V <= J.                      (4.2)

This uses bounded perturbation and the kinetic spectral decomposition, not a claim of analytic regularity of the Coulomb eigenfunction.

Write ell=2B, translate Q to (0,ell)^3, and use the product Dirichlet sine basis in each of the D scalar coordinates. Choose an integer P>=64J/eta, set K=ell P (an integer), and let F retain precisely the modes with 1<=n_j<=K for every scalar coordinate j. Use the same F in every particle coordinate and retain every spin index. It commutes with particle permutations.

Put p=F psi and r=(1-F)psi. Outside F the kinetic eigenvalue is at least P^2/2, because one frequency pi n_j/ell exceeds P. Consequently (4.2) gives

    ||r||^2 <= 4J^2/P^4,
    <r,T_Q r> <= 2J^2/P^2.

Using (H_epsilon-E_epsilon)psi=0 and p=psi-r,

    <p,(H_epsilon-E_epsilon)p>
       = <r,(H_epsilon-E_epsilon)r>
       <= 2J^2/P^2 + 4J^3/P^4.

Our P ensures ||p||^2>=3/4, P^2>=8J, and 4J^2/P^2<=eta/8. Normalizing p, and applying the variational lower bound to every vector in F, proves for the compressed minimum E_F that

    E_epsilon <= E_F <= E_epsilon+eta/8.                     (4.3)

Every retained scalar physical frequency has absolute value at most W=4P, since pi<4. In particular T_Q restricted to F has norm at most T_max=8DP^2. All B_V,G,J,P,W,T_max are bounded by fixed polynomials in L. K can be exponentially large, but log K is polynomial.

## 5. Quadrature soundness on the entire retained space

We now prove the required form estimate, including adversarial states, rather than assume a good witness can be sampled. Extend a Dirichlet sine function oddly across each coordinate of (0,ell)^D to a function on the torus of side 2ell. Multiply by 2^(-D/2) so this extension is an L2 isometry. There is a corresponding even extension of V: in a torus coordinate t represented in [-ell,ell], fold to |t| in [0,ell], translate back by B, and evaluate the original capped potential. The resulting periodic V^ext has norm at most B_V and Lipschitz constant at most G. The coordinate fold is 1-Lipschitz for circle distance, so the Lipschitz claim holds across joins as well. The extended kinetic and potential forms agree with the Dirichlet forms. All these maps act only on spatial coordinates and commute with simultaneous particle/spin permutations.

The extended retained space consists exactly of coordinatewise odd trigonometric polynomials whose integer Fourier frequencies satisfy |n_j|<=K. Choose a power-of-two q so large that

    q>4K,
    h:=2ell/q <= eta/[16D(G+2B_V W+1)].                      (5.1)

There are D position registers each of log_2 q qubits, plus N spin qubits. Since log ell, log P and the logarithms of the polynomial quantities in (5.1) are polynomial in L, this is a polynomial number of qubits.

For any bandlimited spinor f, let S_u f be its samples at the grid points x_j+u, weighted by h^(D/2), where u is any torus translation. Discrete Fourier orthogonality gives

    ||S_u f||_2 = ||f||_2.                                   (5.2)

For completeness, after expanding |f|^2 its frequencies in any coordinate are differences between integers in [-K,K], hence have absolute value at most 2K<q. The discrete sum of exp(2pi i m j/q) is zero except for m=0. This is unchanged by the phase of a shift u. The argument also holds for inner products and spin sums. It is exact and dimension independent.

For normalized f in that bandlimited space,

    ||f(.+u)-f||_2 <= |u| ||grad f||_2 <= W sqrt(D)|u|.

The first inequality follows by integrating the directional derivative along the translation and applying Cauchy–Schwarz (or immediately by Fourier coefficients). Applying (5.2) to the bandlimited difference shows the identical bound for ||S_u f-S_0 f||_2. If u is in the grid cell [0,h)^D, it is at most W D h.

Define the shifted potential quadrature

    A_u(f)=h^D sum_j V^ext(x_j+u)|f(x_j+u)|^2.

Both sample vectors have norm one, and || |v|^2-|w|^2 ||_1<=2||v-w||_2 for unit vectors. Therefore

    |A_u(f)-A_0(f)| <= G sqrt(D) h + 2B_V W D h.

The average of A_u over u in [0,h)^D is exactly the torus integral of V^ext |f|^2, by partitioning the torus into its grid cells. Thus (5.1) gives

    |A_0(f)-<f,V^ext f>| <= eta/16                            (5.3)

for EVERY normalized f in the retained bandlimited space. By homogeneity it is a quadratic-form bound, hence an operator-norm bound on its Hermitian compression. It also holds for mixed states. There is no L-infinity wavefunction norm, no factor involving ell^D, and no high-derivative or trajectory regularity premise. Sampling zeros of odd functions cause no exception, since (5.2) is an exact isometry.

The discrete Fourier transform identifies S_0 with the usual q-point position/momentum registers, and preserves the exact kinetic eigenvalues (pi/ell)^2 sum_j n_j^2/2. Its coordinate reflection j -> -j modulo q corresponds to t -> -t. The common subspace A of (i) signed Fourier frequencies |n_j|<=K, (ii) odd parity in each scalar coordinate, and (iii) antisymmetry under particle permutations, is therefore isometric to the complete retained Dirichlet antisymmetric space. Frequencies 0 and the possible Nyquist frequency are removed by oddness or by the cutoff. No zero- or extra-boundary mode is admitted.

Let E_disc be the least eigenvalue on A of the compressed sum of that kinetic diagonal and the sampled potential diagonal. Equations (3.3), (4.1), (4.3), and (5.3) imply, safely,

    |E_disc-E| <= 2eta.                                      (5.4)

This is the two-sided comparison needed for a verifier. The lower side holds for all valid witnesses, not only for samples of a presumed ground state. The potential need not preserve the Fourier cutoff: only its compressed quadratic form is used.

## 6. Efficient validity projection

We describe ideal projectors, followed by their uniform circuit approximations. All use poly(L) qubits and gates to inverse-polynomial operator error.

The frequency cutoff is checked by applying the inverse discrete Fourier transform, interpreting each register as a signed residue in [-q/2,q/2), and comparing its absolute value with K. Reject if any comparison fails. Uncompute and return to position representation. Coordinatewise oddness is measured by the standard controlled-reflection test for the involution j -> -j mod q, accepting its -1 eigenspace in each of the D coordinates. The cutoff is reflection invariant. Their joint projector also commutes with particle permutations, since the same conditions are imposed on each particle's three coordinates.

Here is a polynomial circuit for the full antisymmetrizer, rather than a promise that the input is already fermionic. Enumerate S_N by its unique sequence of insertion/Fisher–Yates digits d_i in {1,...,i}, i=1,...,N. This encoding has O(N log N) bits and a uniform group superposition can be prepared as the tensor product of the uniform states on each digit range. Let U_perm denote this preparation. Reversibly compute the associated permutation, its parity, and a controlled permutation of the N complete particle blocks (three coordinate registers and one spin qubit each). Multiply by its parity sign, then uncompute permutation data and apply U_perm^*. Accept only if the permutation ancilla returns to zero.

The corresponding accepted operator on the witness is exactly

    A_ferm=(1/N!) sum_{pi in S_N} sign(pi) U_pi.

It is the orthogonal projection onto the sign representation: self-adjointness follows by pi -> pi^(-1), and squaring the sum gives A_ferm^2=A_ferm. A vector in its range satisfies U_pi psi=sign(pi)psi for every pi, and conversely every such vector is fixed. The controlled permutation and reversible digit decoding cost polynomial time; they never enumerate N! permutations. For N=1 this is the identity. Spatial and spin coordinates are exchanged together.

This projection commutes with the earlier joint cutoff/odd projection. Hence the ideal accepted operation is precisely the orthogonal projection Pi_A onto A. If it fails, the verifier rejects. The successful output, for any input density operator including entangled or nonfermionic inputs, is a subnormalized density operator supported on A. Failure has zero acceptance contribution.

Uniform interval superpositions, controlled reflections/permutations, comparisons, and the QFT have uniform polynomial-size approximations in a fixed universal quantum gate set. One explicit way to prepare a uniform interval of size i is a binary decision tree: the probability for either branch is the ratio of the numbers of allowed integers in its two subintervals. Those integer counts and square-root rotation angles are computable to t bits in time polynomial in log i and t. Conditional on a prefix, the counts are computable reversibly, so a depth-O(log i) circuit with arithmetic-controlled rotations avoids enumerating prefixes. The resulting state can be made inverse-polynomially close in norm. Reversing that circuit gives its inverse. Standard gate synthesis and approximate QFT use polynomially many gates for inverse-polynomial operator error. The number of elementary circuit stages here is polynomial, so allocating error delta divided by that number gives total accepted-instrument error O(delta), uniformly over all witnesses. No ideal irrational gate is assumed available exactly.

## 7. Energy measurement, bit complexity and the QMA gap

The position grid has side 2ell and q points; its coordinates are rationals with polynomial bit length despite the possibly exponential values of ell and q. Folding and translating uses reversible integer/rational arithmetic. The input nuclei already have polynomial total bit length. For each of the O(NM+N^2) kernels, compare the squared rational distance with epsilon^2. If it is smaller, output epsilon^(-1); otherwise compute the inverse square root to the needed absolute precision. In the second branch the argument is at least epsilon^2 and at most a number of polynomial bit length. Binary interval bisection/Newton arithmetic therefore has polynomial bit cost. There is no requirement to resolve a near collision below epsilon: that entire branch is capped. Summing the kernels evaluates V^ext to arbitrary inverse-polynomial absolute error uniformly over all grid points.

Similarly, computing the kinetic diagonal from the signed Fourier indices uses the known value pi^2 to polynomial precision. All admitted physical frequencies are at most W, so its necessary absolute accuracy costs only polynomially many bits. There is no multiplication by an uncontrolled high-frequency value after the validity projection. On invalid indices an arithmetic implementation may clamp the value to [0,T_max]; it has no effect on A. The sampled potential is bounded by B_V everywhere.

Threshold extremes are disposed of without large normalization constants. From -C<=E<=0, first accept if b>0 or a>=0; a NO instance is then impossible. If not, reject if a<-C or b<=-C; a YES instance is then impossible. Outside the promise either outcome is allowed. The remaining case has

    -C<=a<b<=0.

Set t=(a+b)/2 and Q_*=T_max+B_V+C+1. In the ideal energy test choose fairly between the following:

* Measure the kinetic diagonal in Fourier representation, with value x, and accept with probability 1/2-(x-t)/(2Q_*).
* Measure the position diagonal potential, with value y, and accept with probability 1/2-y/(2Q_*).

Each probability lies in [0,1]. The overall acceptance probability on a normalized valid state rho is exactly

    1/2 - (tr(rho H_disc)-t)/(4Q_*).                          (7.1)

A probability computed to inverse-polynomial precision can be implemented by an ancillary random-bit register and a comparator (or a synthesized rotation); reversible evaluation and subsequent measurement require polynomial time. Approximate Fourier transforms, parity/group preparation, real constants and these probabilities can all be implemented with total effect on acceptance at most gamma/10, where

    gamma = g/(10Q_*).

This inverse-polynomial target is feasible because the remaining thresholds satisfy g<=C, Q_* is polynomial, and g>=1/L. The total error bound can be imposed directly on (7.1); it does not require simulating unbounded Coulomb time evolution.

For a YES instance, (5.4) supplies a normalized witness in A of energy at most a+2eta. The ideal validity projection accepts it with probability one, and (7.1) is at least

    1/2 + (g/2-2eta)/(4Q_*) >= 1/2+gamma.

For a NO instance, every normalized valid witness has energy at least b-2eta, so its ideal acceptance is at most 1/2-gamma. Any other witness is first projected; its acceptance is the surviving weight times such an acceptance probability, and is therefore no larger. This proves soundness even for arbitrary mixed inputs. The circuit approximation leaves completeness at least 1/2+0.9gamma and soundness at most 1/2-0.9gamma.

Finally repeat the verifier on a polynomial number O(gamma^(-2)) of independent witness registers and take a majority. Completeness uses the tensor power of a good witness and the usual Bernoulli concentration estimate. For soundness against an entangled witness, let the one-register acceptance POVM be B_acc. Its operator norm is at most 1/2-0.9gamma. The majority acceptance operator is the sum of tensor products of B_acc and I-B_acc for the accepting outcome strings. Diagonalizing B_acc separately in each register makes this a classical majority probability with each success parameter at most that bound. Monotonicity and the Bernoulli concentration estimate bound it by 1/3 after a sufficiently large polynomial number of repetitions. Completeness is at least 2/3. Witness length, gates, classical construction time and required precision remain polynomial in L.

This is a QMA verifier for the exact frozen continuum promise problem. Combining it with the stipulated source hardness theorem gives the asserted QMA-completeness. The membership proof itself uses none of the source's engineered-well assumptions.

## 8. Adversarial scope checks and limitations

Nearly coincident nuclei: only M appears in the Hardy and cap estimates; arbitrarily small rational separation is retained. Exponentially distant nuclei: only log B and log q enter qubit/gate counts; unary spatial-grid expansion is never used. Electrons escaping to infinity: (3.2) includes all k, including zero, and the exterior wedge restores exactly N electrons. No binding rate or decay estimate is invoked. All spin sectors: every inequality is componentwise and permutation tests exchange spin too. Malicious ultraviolet/alias witnesses: cutoff is explicitly projected and (5.3) is a uniform form bound; valid low-frequency states cannot create unsampled lower energy. Symmetric or mixed-statistics witnesses: the sign projector rejects the unwanted component before the energy test. Capped collisions: a grid point at a nucleus or electron coincidence is evaluated by the constant cap branch; the uniform Hardy comparison pays the continuum error. Arbitrary thresholds: the preliminary range test prevents exponential rescaling of acceptance probabilities. These are deductions from the displayed proof, not numerical experiments.

The full claim is membership and its hardness corollary, not an algorithm for preparing states, a nuclear-geometry optimization result, a binding theorem, or an unrestricted binary-charge membership theorem. Standard finite-box discretization and quantum verification are antecedents. The proposed contribution is the complete uniform interface linking singular unconfined fermionic input to a sound polynomial verifier. Independent contribution review may judge its substantiality separately from correctness. No Lean or numerical verification is asserted by this packet.
