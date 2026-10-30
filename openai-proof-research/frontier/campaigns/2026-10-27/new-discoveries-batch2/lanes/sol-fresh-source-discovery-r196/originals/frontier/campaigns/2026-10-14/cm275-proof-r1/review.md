# CM275 independent full proof review

**Verdict: PASS_FULL_CM275.** No blocking mathematical objection was found in the complete frozen claim. This is a human full-proof review, not a formalization, novelty verdict, manuscript acceptance, publication approval or campaign count. The author proof is unchanged.

Reviewer relation: this reviewer did not author CM275. The reviewer previously authored TS132 and separate manuscripts and performed other reviews in this campaign; those judgments are not evidence for this proof. The parent supplied a preliminary favorable reading, which was not used as a mathematical premise. A separate contribution gate is required. Original review prose: Myeongjin Kang, no affiliation, CC BY4; original review code MIT; third-party inputs remain private.

## Exact object reviewed

Author directory: `fresh-analytic-discovery-r26`.

- Externally supplied output-manifest SHA256: `957291975356455fcb76bffd1af3fbaad1d344921049b9f9bf7d9ecdd09b2299`.
- Full candidate SHA256: `b467f8b7797ed4c49c4de799399cffab0bc22629b61a0b214ddf2401e8289ffd`.
- Frozen original scope SHA256: `5fe6692d799dd949cfdcd87700a3dd9566acdfa5496080991c0e3d9ccad7fd9f`.

The read-only author verifier was read and independently executed: exact69payload/6directory/31pinned-blob/7PDF authentication passed, and a wrong externally supplied anchor rejected. The three above identities were independently recomputed and are snapshotted. Byte authentication does not establish mathematics.

The result covers every explicitly listed distinct rational unit-charge nuclear configuration, every unary N>=1 and every rational threshold pair with gap at least inverse total input length. The operator is the full spinful antisymmetric electronic Coulomb form on all of R^(3N), with nuclear repulsion omitted. Coordinates and separations have no value bounds beyond their binary descriptions. The spectral infimum may be unbound or unattained. There is no supplied orbital basis, fixed spin sector, confinement, neutrality, binding, eigenvector, preparation or excitation-gap promise. Exponentially large binary charges are not included. None of these quantifiers is replaced by a more convenient subclass.

Upstream Theorem1 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. I checked the actual input and operator statement, not its truth. It matches this exact decision problem and supplies QMA-hardness under deterministic classical polynomial many-one reductions. Membership is proved independently below, making the stated completeness corollary valid under that premise.

The freeze was after the preserved feasibility sketch and primary comparison. The review does not imply that all reasoning occurred after freezing. No new target or repair was substituted during review.

## 1. Forms, energy range and singularity cap

For an H1 spinor, three-dimensional Hardy applies in x_i for almost every choice of the other coordinates and spin indices, also when its center is x_j. Integration and the finite spin sum preserve its constant4. For normalized states, Cauchy–Schwarz gives attraction at most 2sqrt(2)M sqrt(NT). Young with coefficient1/2 yields T/2+4NM², exactly the candidate's C. Thus q>=T/2-C on the full fermionic form domain and on Dirichlet restrictions by zero extension.

The epsilon version makes every attractive and repulsive Coulomb term infinitesimally form-bounded relative to the kinetic form. Consequently the common H1 form domain and lower-bounded closed-form operator are legitimate. The capped potential is bounded and preserves the same form lower bound, since it decreases attraction and retains nonnegative repulsion. The spin sums do not introduce an exponential multiplicative constant.

The upper bound E<=0 follows using disjoint normalized packets of width R and separations at least R², then an isometric wedge. Their kinetic and repulsive energy tend to zero; attraction can be omitted in the upper bound. This does not use attainment or binding. The lower bound E>=-C follows from the form estimate.

For every r>0, 0<=r^(-1)-min(r^(-1),epsilon^(-1))<=epsilon/r². Summing the Hardy estimates counts each nuclear term M times and each electron pair in one chosen coordinate at most N-1 times. The safe coefficient8epsilon(M+N)T in (2.2) controls the absolute difference of both signed parts. Capping repulsion is therefore paid, not silently assumed monotone in the favorable direction. No nuclear separation occurs.

## 2. Nonbinding compactification

The radius R_0=2(1+max||R_alpha||_infinity) contains every nucleus, since sqrt(3)<2. The angle cutoffs have the stated sum of squares and gradient sum. For the product partition, IMS with kinetic normalization1/2 costs at most2N/s². Although there are2^N partition elements analytically, the verifier never computes or enumerates them.

For a fixed subset S, the localized state is antisymmetric among the |S| retained particles, including spin, because all those particles have the same inside factor. Slicing over outside coordinates gives an H1_0 wavefunction on the k-fold inner ball for almost every slice. The trace vanishes on the ball boundary because the inside cutoff vanishes there. Its internal form is bounded below by E_k^ball times its squared norm. Full antisymmetry across inside/outside labels is unnecessary for this sliced inequality and is not asserted.

On outside support the distance to each nucleus is at least s. Removing outside kinetic and all repulsions involving outside particles loses only nonnegative terms, and the remaining attraction is bounded below by -NM/s. Summing the partition and taking arbitrary near-infima gives (3.2), including k=0. The argument does not require a ground state or a quantitative decay rate.

For each k, an arbitrary correlated inner k-fermion state can be wedged with N-k packets supported in disjoint exterior cubes. The one-particle support spaces are orthogonal. Expanding antisymmetrization into support assignments proves the normalization and preserves the internal energy; this works for spinful correlated states, not only Slater determinants. The added packet energy is below15N/s². Every new pair has separation at least s, and there are fewer than N²/2 such pairs. Added attraction is nonpositive. The displayed centers and the choice B>=R_0+(4N+6)s place all supports inside Q.

Therefore E<=E_Q<=E+NM/s+N²/(2s)+17N/s²<=E+eta. For s>=100(NM+N²+N+1)/eta and eta<=1, the last inequality has ample slack. k=0 and k=N are both legitimate. This is a single N-particle box, chosen from the input without knowing the minimizing k. The box may be exponentially long, but its binary description is polynomial.

## 3. Capped Dirichlet eigenvector and spectral cutoff

The cap comparison is two-sided. Low uncapped near-minimizers have T<=2(C+eta+o(1)); low capped near-minimizers have T<=2(C+2+o(1)). Multiplying by alpha=eta/[16(C+2)] gives the forward and reverse errors at most eta/8 in the limiting inequalities, so the recorded eta/4 is safe. Also -C<=E_epsilon<=2.

The bounded capped multiplication operator has norm at most B_V and Lipschitz constant at most G: each one-body term contributes epsilon^(-2), each pair term at most sqrt(2)epsilon^(-2). The candidate's sums safely dominate both. The cube Dirichlet Laplacian has compact resolvent. A bounded self-adjoint perturbation preserves its operator domain and compact resolvent; the fermionic reducing subspace inherits these facts. Thus the capped ground vector is in Dom(T_Q), with ||T_Q psi||<=|E_epsilon|+B_V<=J. No extra smoothness of an uncapped Coulomb eigenfunction is invoked.

The rectangular sine cutoff commutes with kinetic energy and particle permutations. An omitted frequency has kinetic eigenvalue at least P²/2. Applying the bound on ||T_Q psi||, rather than merely on its expectation, gives the stated norm-squared tail4J²/P⁴ and kinetic tail2J²/P². Since (H_epsilon-E_epsilon)psi=0, the projected energy excess equals the remainder energy excess. Its potential part is at most J||r||². P>=64J/eta gives ||p||²>=3/4 and

  (2J²/P²+4J³/P⁴)/(3/4) < 4J²/P² <= eta/8.

This proves the normalized Ritz upper bound; the lower bound holds for every vector by the variational principle. All scalar physical frequencies are below4P, and kinetic norm at most8DP². The mode count is large, but the cutoff's binary description is small.

## 4. Odd extension and all-state quadrature

The coordinatewise odd extension to the doubled torus multiplies by2^(-D/2), making it an L2 isometry. The same factor makes kinetic and reflected-potential expectations identical to the Dirichlet ones. The fold t to |t|, followed by translation, is1-Lipschitz for the circle metric, including its joins. Componentwise folding is1-Lipschitz for the product Euclidean metric. Thus the reflected capped potential keeps G and B_V. All maps commute with particle permutations.

For any retained spinor and any shift, differences of Fourier frequencies have absolute value at most2K<q in every coordinate. Discrete orthogonality therefore proves exact shifted sampling norms and inner products, with no volume or dimension-dependent approximation factor. The shifted difference is itself bandlimited. Its L2 norm is at most |u| times the gradient norm, bounded by W sqrt(D)|u|. For u in a grid cell this is at most WDh. The norm-one sample vectors then satisfy the squared-density l1 bound by twice their l2 distance.

Separating the change in potential and the change in sample vector gives Gsqrt(D)h+2B_VWDh. Averaging over the grid cell reproduces the exact integral. Since D>=1, the stated h makes this at most eta/16. This is a quadratic-form bound for every retained vector, not a statement only about a low-energy witness. Polarization/Hermitian spectral characterization gives the corresponding compressed operator norm bound, and mixed states follow by linearity. No assumed wavefunction supnorm, high derivative or evolving-bandlimit premise is imported.

The Fourier cutoff together with oddness removes the zero and Nyquist modes and leaves exactly the sine space; q>4K leaves no alias ambiguity. Intersecting with full antisymmetry gives the intended space A. The potential need not preserve the cutoff: measurement expectation on A is precisely that of its compression. Adding the four error bounds yields23eta/16<2eta, proving (5.4) in both directions. The NO-instance lower bound is genuinely continuum soundness.

## 5. Validity instrument and circuit uniformity

The cutoff is a comparison in Fourier registers. Oddness is measured by controlled reflection, accepting its -1 eigenspace. Cutoff and all coordinate reflections commute. Individual coordinate odd projectors need not commute with each particle permutation, but their full product does, because the same three-coordinate restrictions apply to every particle. This is exactly the commutation needed for the next stage.

A permutation is encoded by polynomially many insertion/Fisher–Yates digits. Each digit's uniform range state is preparable to inverse-polynomial norm error with polynomial arithmetic and rotations. Reversible decoding, parity and controlled permutations of N complete particle blocks cost polynomial time (an adjacent-swap implementation already suffices). No N!-term enumeration occurs. Uncomputation and accepting the ancilla at zero implement the group average (1/N!)sum sign(pi)U_pi. Inversion and the group law make this the orthogonal sign projector. Its range is exactly simultaneous spatial-spin antisymmetry, including N=1.

Because that projector commutes with the full previous projector, the accepted Kraus operator is Pi_A. An arbitrary, possibly entangled or wrong-statistics input therefore contributes a subnormalized state Pi_A rho Pi_A. Rejection has zero acceptance contribution. This is a legitimate verifier instrument, not free postselection.

The ideal preparation/QFT/rotation descriptions have polynomial fixed-gate-set approximations. Arithmetic-controlled interval rotations can be implemented by reversibly computing the prefix counts and an angle, then using controlled rotations on angle bits; there is no branch enumeration. Allocate an inverse-polynomial error budget among polynomially many stages. Telescoping the dilated circuit approximations bounds the total acceptance effect uniformly on every witness, before any conditioning. Invalid-register arithmetic is defined and bounded; in particular the kinetic value can be clamped off the accepted band. Thus a tiny acceptance probability in an invalid input cannot amplify a gate approximation error.

## 6. Arithmetic, gap and amplification

M,N<=L and eta^(-1)<=100L, so C,B_V,G,J,P,W,T_max and Q_* are polynomial-valued when the least admissible integers are chosen. Rational ceiling and power-of-two choices are computable in polynomial time. log B, log K and log q are polynomial even for exponentially distant nuclei. No grid or basis enumeration is used; each coordinate needs log q qubits.

Rational folded grid positions and squared distances have polynomial bit length. Comparing with epsilon² is exact rational arithmetic. Below the cap, including exact coincidence, evaluation returns epsilon^(-1). Above it, inverse-square-root approximation to fixed absolute precision is uniformly polynomial: one can bisect the output interval [0,epsilon^(-1)] using rational squared comparisons. There are polynomially many kernels, so summation at suitable per-term precision works uniformly. Kinetic evaluation uses indices of polynomial bit length and physical frequency at most W; pi² approximation therefore has polynomial precision cost. The branch probability circuits consequently have the claimed uniform accuracy.

The preliminary threshold decisions respect the promise: b>0 or a>=0 excludes a NO instance, while, after these are removed, a<-C or b<=-C excludes a YES instance. In the remaining case -C<=a<b<=0. Both diagonal-test probabilities lie in [0,1] with Q_*=T_max+B_V+C+1, including the clamped off-band kinetic branch. Averaging the two tests gives exactly (7.1).

Since eta<=g/100, g/2-2eta>=0.48g. Dividing by4Q_* gives at least0.12g/Q_*, exceeding gamma=g/(10Q_*). A uniform acceptance error at most gamma/10 preserves the stated0.9gamma completeness/soundness margins. For invalid witnesses the surviving weight multiplies a nonnegative valid-state acceptance probability, so the upper bound remains valid. The inverse gap is polynomial.

For repetition, the one-register acceptance effect has norm at most1/2-0.9gamma on NO inputs. The majority effect is a sum of tensor products of this effect and its complement. Their common product eigenbasis reduces its maximum eigenvalue to the maximum Bernoulli majority probability with each parameter at most that bound. Monotonicity and concentration give soundness even for entangled witness registers. Tensor copies of a good witness give completeness. A polynomial number of repetitions yields2/3 versus1/3 without a witness independence promise.

## Required corrections and nonblocking clarifications

There are no required mathematical repairs. Future exposition should make the least-admissible ceiling choices explicit, and may spell out the group-decoding implementation and the finite-band sampling normalization, but each is already specified sufficiently for the proof and does not change any scope or operation. The main limitations must remain visible: the theorem is membership, not efficient witness preparation; no binary exponentially large-charge extension is proved; the proof is human mathematics and has not been fully formalized.

The cited primary comparisons support the description of antecedent interfaces, not worldwide priority. This review does not decide whether the combination is a substantial contribution. Detailed actual reading ranges and provenance are recorded separately. The final packet's checksum certifies its immutable bytes only.
