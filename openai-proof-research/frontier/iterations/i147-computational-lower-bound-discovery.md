# I147 — Original I144 audit and computational lower-bound discovery

**No nomination. Eight accepted substantial findings remain eight; two remain.** Original I144's paid assertions below **PASS without repairs**, with their original constants and hypotheses. General P138 is **unproved/unrefuted and PARKED** after this audit. The fresh screen retains a proved technical partial: expected measured outputs of fixed-depth QAC0 circuits have small heat-bath Dirichlet energy under two classes of correlated classical Ising input distributions. Two different proofs give explicit constants. The more ambitious computational targets remain parked; neither the technical deduction nor a change of wording is counted as a substantial ninth finding.

All OpenAI theorems and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. External literature is ordinary evidence. No upstream truth audit, contradiction inference, ex-falso, children, shared edits, staging, commits or publication. I145/I146 are not dependencies. The Ising measure below is a distribution of **classical circuit inputs**, not the parked quantum thermal target, a physical noise channel, or an entangled-game problem.

## 1. Original-context gate and inherited failures

The raw original I144 task has SHA-256 `ad9fe4a0d4d5594dadbab94ab79ba2d72f3c5b9cc97f47b8811e8346f5c97d94`. All decoded fields of it and the recursively required original I120/I123/I126/I129/I132/I135/I138/I141 tasks were frozen and read before assigning the audit. This includes original briefs, full embedded reports, finalized parent responses, objections, escaped JSON stdout and repeated structured results. The lossless decoded representation separates 2,811 distinct literal string lines from their ordered occurrences and 525 distinct scalar-key/value pairs from 1,696 scalar occurrences. Repeated content was read once, while exact occurrence paths and multiplicities remain recorded. JSON embedded in strings is decoded recursively, including the complete trailing parent JSON in each brief. This is not a brief-only or four-ledger-only substitution. Earlier truncated displays are recorded; smaller supplied ranges recover the complete decoded view. Historical `running` fields are retained literally and are not mathematical verdicts.

The actual I144 report and finalized parent receipt are frozen separately. The I144 task's embedded I141 report and parent response are checked against their separately frozen originals; the later I144 report and receipt are bound independently. AGENTS.md, upstream identity, catalogue and four live ledgers are frozen; only relevant ledger passages were semantically read. Only the four original live ledger paths may drift. Snapshots, original task records, receipts and mathematical sources may not. Parent review was selective, not the independent original-proof pass here.

Preserve the literal original endpoint-only I129 R2 **FAIL** (`chi=2` and identical point masses) separately from corrected `0<=chi<=1` R129-cutoff **PASS**. Preserve I114's qualified thermal statements and all failures of arbitrary finite-energy differentiability, bounded inverse, arbitrary-state stationarity, weighted-Q and ordinary-R bounds; the external Cuesta scalar-factor defect is not erased. I126's joint-law condition `n theta_n -> 0` stays distinct from the sufficient expectation/UI condition `theta_n n^(4/3) -> 0`. I135 retains its source-dependent subpower gauge, prescribed prefixes and the constants `pi T_2^2+1/2`, `4pi M^2/(lambda-B)^2`, `pi L^2+64pi M^2(log 2)^(-gamma)[1+1/(gamma-1)]`, and pole coefficients `pi/2, pi/4`; no uniform logarithmic Brennan endpoint follows. I138 retains finite jets versus caustics, simple-graph outgoing rates, all-active slopes, nonnested boxes, and its separate stronger-claim counterexamples. Original I141 F1–F4/R1–R7, the integrated reverse-flux obstruction and uncertified RK4 exploration retain their original scope. No inherited numerical run is repeated. All other parked branches remain parked.

## 2. Independent audit of ORIGINAL I144, unchanged

### 2.1 Ring A1–A5 — PASS without repairs

Use the original six complexes `y0=(2,1,0), y1=(1,2,0), y2=(0,2,1), y3=(0,1,2), y4=(1,0,2), y5=(2,0,1)`, both directions on consecutive edges, total mass one. For `w=B+C`, the **exact** derivative is

`w' = k01 A^2 B + k54 A^2 C + k12 AB^2 + k43 AC^2 - k10 AB^2 - k45 AC^2 - k21 B^2 C - k34 BC^2`.

Edges 05/50 and 23/32 have zero total-rare increment. Thus discarding only positive terms gives precisely the original inequality. The complete harmful polynomial is

`AB^2+AC^2+B^2C+BC^2=(1-w)(B^2+C^2)+BCw <= w^2`.

Each coordinate has four consuming directed edges, with decrement one; every degree-three source containing that coordinate is at most that coordinate on the mass-one simplex. Hence `C=4K,d=3` is valid. In particular `w'>=-Kw^2>=-Kw` globally. This is a bound on the physical derivative, not an averaged surrogate.

Keep **exactly** `a=(alpha/4)exp(-4KT)`, `rho=min(1/2,a/[8KT exp(2KT)])`, `q=min(1,a/2)`, `delta_v=rho exp(-KT)`. On a whole length-T window with `w<=rho`, `A>=1/2`; individual consumption gives `B(u)>=exp(-4KT)B(s)` and likewise C. Independent every-window PE therefore bounds the sum of the two actual useful flux integrals below by `a w(s)`. If the endpoint doubles, its increment exceeds `w(s)`. Otherwise backward integration of the scalar lower differential bound gives `w(u)<=2exp(KT)w(s)` throughout, so the whole harmful integral is at most `4KT exp(2KT)w(s)^2 <= a w(s)/2`. Both cases give original A1, increment at least `q w(s)`.

For `w_Q=min_Q min(1-A,1-B,1-C)>0`, retain A2:

`tau_v=T[1+ceil(rho/[q min(rho,w_Q)])]`.

If a trajectory starts below rho and has not reached it, complete-window endpoints increase by at least `q min(rho,w_Q)`. The loose extra window in A2 pays finite exit. Starting at rho or hitting rho at a window endpoint already completes exit. After reaching or starting above rho, each connected later excursion below rho has a left endpoint at rho. If its duration were at least T, A1 on the first closed T-window would contradict an endpoint at most rho. This excludes duration exactly T as well. Consumption within every shorter excursion gives delta_v. Taking the common maximum already embodied in w_Q proves **all three pair-sum floors simultaneously for every t>=tau_v**, not only period endpoints.

The vertex-to-edge step retains `gamma=alpha exp(-16KT)`, `m=delta_v/2`, `r=min(m,gamma m^3/2)`, `delta=r exp(-4KT)`. For any `s>=tau_v`, a coordinate B at least r retains delta at s+T. If B is below r, both A and C are at least m by the pair-sum floors at s. The real edge `y5->y0` produces one B from `A^2 C>=m^3`; F2 gives at least `gamma m^3>=2r>=delta`. Cyclic copies pay the other two coordinates. Restarting the estimate at `s=t-T` proves A5 at **every** `t>=tau_v+T`. The floor depends only on K,T,alpha; the time additionally depends on compact Q. No assertion of a fresh-schedule invariant polygon is needed.

### 2.2 Restricted theorem A144, A6–A10 and examples — PASS without repairs

The criterion is finite and correctly restricted: every **accessible proper siphon** Z in the fixed mass-one class must have, from each rare species, a path in the actual first-order-in-Z species graph to a source whose product rare count is at least two. Class-face accessibility is part of the criterion; weak reversibility alone does not imply it.

If a weakly reversible edge has source meeting a siphon Z but product disjoint from Z, a return path has a first edge introducing Z from a disjoint source, contradicting the siphon definition. Consequently a negative total-rare increment cannot have rare source count zero or one. Its integer rare count is at least two. All coordinates are at most one, so **every** harmful source monomial is at most `w_Z^2`, including higher-order sources and nonrare factors. The unchanged `D_Z=max(1,K sum_e(-b_e)_+)` bounds their full sum. Thus `w_Z'>=-D_Z w_Z^2>=-D_Z w_Z`.

In a patch with all outside coordinates at least m, a first-order source from j is `x_j` times nonrare factors, bounded below by `m^d x_j` at the relevant start. A simple transfer path has length at most `r_Z-1`. Each transfer has a different receiving coordinate, source exponent zero there and product coefficient at least one. F2 propagates the bound by `gamma m^d`, with `gamma=alpha exp(-C(d+1)T)`. Padding uses old-coordinate retention, not a fictitious reaction. The original constants

`beta=min(1,exp(-CT),gamma m^d)`, `H_Z=r_Z T`, `G_Z=(gamma m^d/r_Z) beta^(r_Z-1)`

are therefore valid: start at a coordinate at least `w_Z(s)/r_Z`, transfer and pad for `r_Z-1` windows, then apply F1 on the marked branching edge in the last window. F1's factor is at least gamma, so its **physical positive rare-mass flux** is at least `G_Z w_Z(s)`. Independent PE on successive windows pays ordering even if a required edge also fired earlier. Other positive terms can be dropped; all negative terms remain charged.

On a whole H_Z-window staying in the patch, scalar nondoubling gives `w_Z(u)<=2exp(D_Z H_Z)w_Z(s)`. Retain exactly A7:

`rho_Z=min(m,1/2,G_Z/[8D_Z H_Z exp(2D_Z H_Z)])`, `q_Z=min(1,G_Z/2)`, `delta_Z=rho_Z exp(-D_Z H_Z)`.

The integrated loss is at most `4D_Z H_Z exp(2D_Z H_Z)w_Z(s)^2`, hence at most half the useful contribution. Doubling gives the other case. The scalar exit/excursion argument includes endpoint equalities and arbitrary late excursions, conditional on the outside-coordinate patch.

A8–A10 actually supply that patch, through **all subsets**, not merely minimal siphons. Starting with `delta_n=1,tau_n=0`, the induction hypothesis for every (r+1)-set gives, whenever `w_Z<=m=delta_(r+1)/2`,

`x_j=w_(Z union {j})-w_Z>=m` for every j outside Z.

An inaccessible face has a strictly positive compact minimum of w_Z. A non-siphon has a source disjoint from Z and product meeting Z, with positive integer rare increment; if w_Z starts below m, its complete source is at least `m^d`, while above m the sum retains `exp(-CT)m`. This gives the stated rolling T-delay and floor even if the patch is later left.

For an accessible siphon at the deterministic stage start `tau=tau_(r+1)`, global consumption gives `w_Z(tau)>=exp(-C tau)u_Z`, `u_Z=min_Q w_Z>0`. The original A9 delay

`B_Z=H_Z[1+ceil(rho_Z/[q_Z min(rho_Z,exp(-C tau)u_Z)])]`

is valid. All larger-set floors persist for every later time, supplying the patch in every future small-w_Z excursion. Taking the finite maximum of delays and minimum of floors gives A10. The times may depend on Q; induction shows the floors do not. Every reset time is deterministic and may have arbitrary PE phase. Exactly n-1 stages give eventual coordinate floors for all future times. There is no all-initial uniform time or fresh-schedule invariance hidden here.

The one-direction ring is weakly reversible and includes transfer-before-branching paths, e.g. near A, `C -> B` via 50 and B branches via 01. In the complete bidirected family of complexes `2e_i+e_j`, n>=3, the reaction span contains every `e_j-e_i` and has rank n-1. Proper siphons are exactly the sets with one outside species: two outside species support a rare-free source able to produce Z, whereas one outside species supports no complex. These siphons are accessible and critical; each j has the branch `2e_a+e_j -> e_a+2e_j`. Thus this is an unbounded-rank family, not a scalar case. Doubling every ring complex removes every first-order rare source but preserves the critical geometry. It defeats the criterion, **not** the permanence conclusion.

### 2.3 B1–B3 endpoint coefficients and labels — PASS without repairs

With endpoint `z=x(s+T)` and coordinatewise `z_i<=L x_i(s)`, L>=1, forward and backward consumption give

`exp(-CT)L^(-1)z_i <= x_i(u) <= exp(CT)z_i`.

The exact physical coefficients `q_e=(T z^y_e)^(-1) integral k_e x^y_e` satisfy

`(z-x(s))/T=sum q_e z^y_e Delta_e`,
`a_L=(alpha/T)(exp(-CT)/L)^d <= q_e <= b=K exp(CdT)`.

Degree-zero sources have no monomial factor and satisfy the conservative common bounds as well; feasibility implies alpha/T<=K. The upper endpoint coefficient needs no B1. The lower one does. Neither is an upper coefficient at the initial monomial.

The complete October affine operations were checked, including all coordinate directions and complex differences, fixed slopes and separation H, raised-coordinate types, compensating offsets, closed active sets and overlapping interval gluing. With c on the plateau, endpoint `z in B_h`, and `|R| b h^H<=a_L/2`, the ordered-cut estimate applies to this actual q-vector. At every active endpoint slope it is nonnegative; outside the plateau every such slope is outside S-perp, a crossing gap is at least 2H, and source monomials in the box are at least h^d, giving at least `a_L H h^d`. Empty graphs have singleton classes, so the strict case is vacuous.

For **any** endpoint active affine branch, the orientation is

`F_h(z)-F_h(x(s)) = ell_r(z)-F_h(x(s)) >= ell_r(z)-ell_r(x(s))`.

This proves B3, including every tied endpoint label and any number of interior switches. The start need not be in the box for this inequality; the endpoint must. It proves no bounded loss on windows failing B1 and no general return to that box.

### 2.4 B4 schedule, exact amplification and method scope — PASS without repairs

The twelve-slot schedule has `T=1/100`, `ell=1/1200`, one directed edge at rate one per slot, period T. Every shifted length-T integral of each edge is exactly ell: the tail and head partition a full period. With 05 first and `a=1-epsilon`, the exact physical solution on that slot is

`A=a`, `B=(epsilon-epsilon^3)exp(-a^2 t)`, `C=epsilon-(epsilon-epsilon^3)exp(-a^2 t)`.

Thus `C(ell)/epsilon^3` diverges, and later consumption retains `C(T)>=exp(-4T)C(ell)`. Also `A(T)>=exp(-4T)a`, paying unbounded amplification of the actual monomial A^2 C. Globally each positive rare-mass source is at most w and its coefficient is one, so the safe bound `w'<=12w` gives `w(t)<=exp(12T)epsilon<2epsilon` throughout. Scalar nondoubling does not imply B1 for any fixed L.

The separate split `B(0)=(epsilon/2)exp(a^2 ell/2)` has positive C and reaches B=C exactly at ell/2, illustrating a switch of `min(B,C)`. This is expressly not an identification with the source F_h. The example is a **method obstruction only**: A5 already establishes permanence of this very schedule. No finite-window amplification is promoted to extinction.

**Audit separation:** no new FAIL among original I144 paid assertions; inherited literal failures remain failures. General P138 and the unrestricted coordinate-ratio/reset mechanism are **unresolved**, not false. A144 and B3 retain their restricted scopes and technical contribution classification. The original parent checks were not used as substitutes for this audit.

## 3. Full source contracts and overlap screen

The actual mathematical sections of both family-243 papers, both family-274 papers, and all six sections of family 284 were read through their endings. The exact paths, hashes and supplied ranges are in `read-manifest.json`; catalogue numbers served only as leads.

**243.** Full CPT+C uses arbitrary-rank hereditary finite sets over unordered atoms, exact counting and polynomial bounds on time and intermediate transitive size. The separation is an isomorphism-invariant polynomial-time query on all finite structures of a fixed eight-relation vocabulary. The hard paired structures encode inconsistent versus consistent F3 systems on grids, not ordered matrix encodings. The complete lower mechanism includes a nonabelian automorphism group with central F3 subgroup, rank-independent supports, base counting equivalence and homogeneity, arbitrary-rank HF counting transfer, quotient interpretations, exact trace coding of size at most `9B^3`, and matching halt/output formulas. A supplied linear order changes the problem. The companion gives one fixed witnessed-symmetric-choice occurrence with an all-input guard, polynomial histories, history-stabilizing automorphism witnesses and Boolean default behavior on malformed inputs. Its separation lower bound treats actual evaluated arguments and intermediate candidates. It does not give free arbitrary choice or a time hierarchy/undecidability theorem.

**274.** The strongest operation is uniform product-projection localization, not merely worst-case parity. For fixed reflection depth d and fixed `0<=s<t`, all sufficiently large total qubit counts N satisfy

`||[M>=N^t] U[D=0]U* [M=0]|| <= exp(-N^s)`                 (L)

for every allowed U and every pair of mismatch counts with arbitrary one-qubit reference vectors and arbitrary counted subsets. The threshold depends only on d,s,t. The proof operations include polynomial filters, exchange of counted/projected registers via the inverse circuit, depth reduction and bootstrap. The regular-trajectories companion pays propagation, transport and pruning. The consequences already include **full uniform-input scalar Fourier concentration**, high-average-accuracy majority obstruction, state-preparation bounds and measured-output-to-clean reductions under their stated interfaces. A uniform-input noise-sensitivity restatement is therefore spent. Worst-case strict-majority advantage is not a constant average-case correlation lower bound.

**284.** For each fixed integer k>=2, the explicit total construction on allowed lengths has

`R_(1/3)(F_(k,m)) >= c_k m^(2-1/k)/(log m)^2`,
`Q_(1/3)(F_(k,m)) <= C_k sqrt(m)(log m)^(b_k)`.

Malformed certificates are assigned a Boolean value; the construction is not left as a promise relation. The full quantum verification/tournament procedure pays capped bad branches. The randomized proof uses the posterior-sensitive block lower operation and dummy hidden winner, with a completion budget of the form `4G/m^2+G/(mL)+G(2/3)^r`; multiplying naive independent success probabilities would not reproduce it. The upper comparison uses block sensitivity, degree and spectral sensitivity. The exponent supremum is four. This does not supply a single family with an exact fourth-power inequality, remove logarithmic losses, bound computational running time by query count, or make the heterogeneous bit positions transitive.

Project overlap was checked in I103 and I106/I109 followups (algebraic formulas/IMM, characteristic and exact degeneration issues), I80/I85/I86 (fluid computation and its separate novelty limitations), I114 (quantum information), and early scoped screens. None is a premise for the new inequalities. In particular I114 already pays polylogarithmic-precision Boolean-oracle synthesis from the complete family-283 operations; it is excluded here. Early matching-PSD perturbation and quantum-code screens have different models and retained obstructions. No active I145/I146 output is read or bound.

## 4. Three quantified targets

### T1. Correlated-input circuit stability — proved technical partial, developed below

For every fixed d,c>=1, a0>=0 and epsilon>0, consider all n-input circuits of reflection depth at most d with `n<=N<=n^c` total qubits, zero ancillas, arbitrary one-qubit gates and unbounded Toffoli gates. For every Ising measure with a finite real field vector on n classical spins with real symmetric zero-diagonal interaction J satisfying `lambda_min(J)>=-a0`, ask whether its stationary rate-one-per-site heat-bath chain satisfies

`sup_(C,J,h) E[(f_C(X_(n^-epsilon))-f_C(X_0))^2] -> 0`.

Here `f_C` is the expected measured sign of one designated output, and arbitrary other outputs may be discarded. The supremum includes nonuniform circuits, arbitrary finite fields depending on n and dense signed J. No mixing or high-temperature hypothesis is imposed. Routes A and B below prove this target, Route A under a different graph-coloring hypothesis. They also give an explicit conditional distributional lower-bound interface. Contribution is assessed separately.

### T2. Total bit-transitive quartic separation — PARK

For every fixed epsilon>0, seek an explicitly and polynomial-time uniformly evaluable family of **total** Boolean functions F_m on an infinite constructive sequence of input lengths, each invariant under a polynomial-time generated transitive permutation group on **all bit positions**, such that `Q_(1/3)(F_m)->infinity` and

`R_(1/3)(F_m)/(1+Q_(1/3)(F_m))^(4-epsilon) -> infinity`.

Both costs are worst-case bounded-error **bit query** complexities; computation between queries is unrestricted. This does not ask for an exact fourth-power bound. The pinned quartic function has distinct data, address, transcript and pointer roles. A restriction or a permutation of these roles does not itself prove bit transitivity. OR-ing over all relabelings can destroy the desired quantum cost and certificate structure; promising a valid encoding would discard totality.

Chakraborty–Kayal–Paraashar's 2025 transitive-functions paper was read at its theorem/table and complete Section 4 construction, including the balanced-pointer encoding and coupled group action prerequisites. Its encoding is tailored to preserving pointer certificates. The randomized-versus-quantum table entry supplies a quadratic separation against a quartic general upper bound; the quartic **deterministic**-versus-quantum entry is a different statement. Bansal–Sinha's explicit Forrelation result is a partial-function lower bound; its total-function consequence is cubic. Their Gaussian/Fourier method is not a totality-preserving transitive compiler. No such compiler or new transitive lower distribution was constructed here. This is a precise unpaid interface, not evidence that T2 is impossible.

### T3. Growing individualization in the actual unordered F3 models — PARK

Let L be the side length of the actual three-dimensional box grid and k=floor(L^(1/4)). Choose an ordered list of k distinct grid edges T, and a vertex v_* in a component of G minus T containing more than L^3/2 vertices. In each of the pinned structures A_0 and A_(1_{v_*}), mark the k edge atoms (e,0,0), in exactly that chosen order. Expand the fixed eight-relation vocabulary by a unary predicate for this list and a binary linear order **only on its marked atoms**. The coordinates (e,0,0) specify the external construction; they are not additional input labels. Seek: for every fixed CPT+C sentence psi in this fixed expanded vocabulary, there exists L_0(psi) such that for every L>=L_0, every such ordered T and every such v_*, the two expanded structures agree on psi. This specifies the pairing and giant-component promise explicitly, and excludes a locally exposed defect behind a fully marked cut. No order is supplied on the other atoms; arbitrary HF rank and exact counting remain allowed.

Fixed-length tuples and routine definable interpretations are already covered by the complete lower operations and are not nominated. A direct attempt symmetrizes a trace over the full original group after running with marks. The mark stabilizer has index at most exponential in k (the local fibre dimension is bounded); writing this as `3^(O(k))`, the old support budget becomes `O(L(k+log N)^2)`. The corresponding available homogeneity width grows like `O(L^(3/2)(k+log N)^3)`. At k=L^(1/4) this crude route reaches L^(9/4), exceeding the grid-scale L^2 budget. Even the extrapolation to smaller k would require paying the named-list interpretation and paired support games; it would be a parameter extension, not a substantial target by itself. For T3 the missing estimate is a support/homogeneity bound for the marked stabilizer that avoids this blowup, or a genuinely different argument. No such estimate or refuting CPT program is obtained.

Lichter–Schweitzer's WSC canonization implications concern their expanded choice logic and classes closed under individualization, not the requested growing-mark lower bound in CPT alone. Pago's symmetric-XOR lower operation explicitly has symmetry/connectivity restrictions and distinguishes CFI-symmetric or symmetric-basis computations from unrestricted CPT. Its theorem cannot be silently applied to the actual arbitrary-rank F3 program traces. These primary comparisons prevent claiming a generic finite-model robustness result from noncapture alone.

## 5. T1: the exact circuit and probability interfaces

Retain the N-wire unitary circuit, including discarded wires as idle wires. A layer consists of disjoint product-state reflections, interleaved with arbitrary local unitaries; Toffoli is such a reflection. The inverse remains at the same reflection depth. No fanout, controlled version of an arbitrary one-qubit gate, clean coherent computation, input-dependent advice or entangled ancilla is added. For output t let

`Q=C* (|0><0|_t) C`, `f(x)=2<x,0|Q|x,0>-1`.

Then f is in [-1,1] and its correlation with a Boolean sign target is twice the measured success probability minus one. This definition averages the output measurement. Independent fresh measurements could disagree even on an unchanged input, so the noise theorem is not a bound on that additional randomness.

### 5.1 Uniform biased-product bridge

For a product law with input-one probabilities p_i in (0,1), set

`v_i=sqrt(1-p_i)|0>+sqrt(p_i)|1>`,
`w_i=sqrt(p_i)|0>-sqrt(1-p_i)|1>`.

For h in {0,1}^n, multiply both vectors at coordinate i by Z^(h_i). For S use w on S and v elsewhere, obtaining the orthonormal vectors w_(S,h); let v_h=w_(empty,h). Averaging the matrix entry `<w_(S,h),0|Q|v_h,0>` over h kills every off-diagonal computational-basis term. The remaining coordinate factors are the product probabilities times

`chi_i(x_i)=(p_i-x_i)/sqrt(p_i(1-p_i))`.

Thus for nonempty S the biased Fourier coefficient of f equals twice this phase average. For fixed h the vectors w_(S,h) have mismatch count |S| relative to v_h. Jensen, Bessel and **the full localization operation (L)** give, for all sufficiently large N and integer k>=N^t,

`sum_(|S|>=k) |fhat_p(S)|^2 <= 4 exp(-2N^s)`.             (P)

The threshold is uniform in every p_i, even if they approach zero or one with n. Deterministic coordinates follow by restriction/limits. Restricting any input coordinates fixes actual product states and leaves the physical N and d unchanged. This proof adds no gates: its phase vectors are analytical test vectors. It extends the source's uniform phase average to arbitrary product weights; that extension alone is a direct technical use of the stipulated operation and is not nominated.

Let `D_p(f)=sum_i E_p Var(f | all coordinates except i)`, the Dirichlet form for rate-one product resampling at each site. The biased Fourier basis gives exactly

`D_p(f)=sum_S |S| |fhat_p(S)|^2 <= k+4n exp(-2N^s)`.       (D)

The total Fourier weight is at most one. These are absolute tails and energies, not ratios to Var(f).

### 5.2 Route A: color-class conditioning

Let `mu(sigma) proportional exp(1/2 sigma^T J sigma+h.sigma)` with finite real couplings and fields. Suppose the interaction graph admits q independent color classes. Conditional on all spins outside one color class I, spins in I have a product distribution with arbitrary effective fields. Applying (D) to the restricted circuit, uniformly in the conditioning assignment, bounds the sum of the physical conditional variances for i in I by

`k+4|I| exp(-2N^s)`.

Averaging and summing the q classes proves

`D_mu(f) <= q k+4n exp(-2N^s)`.                          (A)

The conditionals here are exactly the heat-bath conditionals given all other spins. This pays the passage from a product estimate to the correlated physical dynamics. There is no coupling-size, sign, high-temperature, uniqueness or mixing requirement. This is useful for fixed or sufficiently slowly growing q, even when individual couplings diverge. It does not by itself cover dense graphs with growing chromatic number.

### 5.3 Route B: Gaussian mixture and an edgewise conductance inequality

Assume J is symmetric with zero diagonal and put `a=max(0,-lambda_min(J))`, `A=J+aI>=0`. Adding this diagonal changes the Hamiltonian by a constant. Let phi_A be the centered Gaussian probability measure with covariance A, possibly singular, and define

`nu(dz) proportional [product_i 2cosh(h_i+z_i)] phi_A(dz)`,
`mu_z(sigma)=product_i exp((h_i+z_i)sigma_i)/(2cosh(h_i+z_i))`.

The Gaussian moment-generating identity gives **exactly** `mu=integral mu_z nu`. Every integral is finite. The factorization itself is classical Hubbard–Stratonovich material; it is not a claimed invention.

One cannot simply identify the mixture's product heat-bath form with the physical Ising form. Here is the needed comparison, for every real function F on the cube:

`kappa(a) D_mu(F) <= integral D_(mu_z)(F) nu(dz) <= D_mu(F)`,
`kappa(a)=exp(-a/2-sqrt(2a/pi))`.                         (G)

To prove it, fix a site i and all other spins eta. Write `b=h_i+sum_(j!=i) J_ij eta_j`. In the joint law of z and sigma, conditioning on eta tilts the base Gaussian by `exp(sum_(j!=i)eta_j z_j) cosh(h_i+z_i)`. Gaussian linear tilting changes the mean of theta=h_i+z_i to b before the cosh tilt, and its variance is A_ii=a. Therefore theta has the law N(b,a), reweighted by `cosh(theta)/(exp(a/2)cosh b)`. This remains valid for singular A, by its moment-generating identity or a vanishing positive diagonal approximation.

If Delta=F(eta,+)-F(eta,-), the physical conditional variance is `Delta^2/(4cosh^2 b)`. The averaged product conditional variance, with the correct posterior of z given eta, is

`Delta^2 E_(G~N(b,a))[sech G]/(4 exp(a/2)cosh b)`.

Their **exact edge ratio** is

`r_a(b)=exp(-a/2)cosh b E[sech(b+sqrt(a)Z)]`, `Z~N(0,1)`.

Since `cosh(b+u)<=cosh b exp(|u|)`,

`r_a(b)>=exp(-a/2) E exp(-sqrt(a)|Z|)>=kappa(a)`.

The second inequality is Jensen, with E|Z|=sqrt(2/pi). The upper bound r_a(b)<=1 is conditional variance decomposition in the joint mixture. Multiply by the outside marginal and sum the edges to prove (G). At a=0 all these identities and the constant reduce continuously to one. No lower bound on the fields or on single-spin probabilities is used.

Integrate (D) over this mixture and use the **lower** comparison in (G):

`D_mu(f) <= exp(a/2+sqrt(2a/pi)) [k+4n exp(-2N^s)]`.      (B)

The constant depends only on the negative spectral edge. Positive eigenvalues may grow, the graph may be dense, fields may be arbitrary and interactions may have either sign. No log-Sobolev constant or mixing-time estimate is asserted. This mechanism differs from coloring: it handles dense graphs with bounded negative spectral edge, while (A) handles bounded-color graphs without a spectral bound.

### 5.4 Stationary noise and a distributional lower-bound interface

Let `L=sum_i(E_i-I)` be the continuous-time heat-bath generator, each site updating at rate one. It is self-adjoint and nonpositive on L2(mu); `D_mu(F)=<-L F,F>`. For its stationary pair (X_0,X_u),

`NS_u(F):=E(F(X_u)-F(X_0))^2 = 2<F,(I-exp(uL))F> <= 2u D_mu(F)`. (N)

Fix epsilon>0, d,c,a0. Choose `delta=min(epsilon/2,1/2)`, `t=delta/(2c)`, `s=delta/(4c)`, `k=ceil(n^delta)`. Then `N^t<=n^(delta/2)<=k`, and `N^s>=n^s`. All thresholds depend only on d,c,epsilon. Equations (B),(N) imply uniformly for a<=a0

`NS_(n^-epsilon)(f) <= 2 exp(a0/2+sqrt(2a0/pi)) n^-epsilon [ceil(n^delta)+4n exp(-2n^s)] ->0`.

This proves T1. Equation (A) proves the parallel assertion for fixed q with no interaction-size assumption. The same displayed estimates state precisely what remains true for growing q or a; no uniformity in changing depth is inferred.

There is also a useful exact lower-bound interface. For any Boolean sign target g, reversibility and Cauchy–Schwarz give, with P_u=exp(uL),

`|<f,g>| <= ||f-P_u f||_2+||P_u g||_2 <= sqrt(NS_u(f))+sqrt(<g,P_(2u)g>)`. (C)

Indeed `(1-exp(-v))^2<=2(1-exp(-v))`, and `||f||_2<=1`. Thus any specified target/distribution family with `<g,P_(2n^-epsilon)g> ->0` has measured average success at most `1/2+o(1)` against these circuits. The autocorrelation includes the squared mean; balancedness cannot be omitted. More generally the stationary-pair triangle inequality gives

`1-<f,g> >= [(sqrt(NS_u(g))-sqrt(NS_u(f)))_+]^2/8`.

These are explicitly **distributional** conclusions, not a worst-case parity premise being promoted to an average-case bound. They concern total Boolean targets whenever g is total; no query-complexity or running-time assertion is made.

The current Tassion–Vanneuville Ising-crossing paper supplies a promising concrete target: its introduction states a polynomial-scale high-temperature crossing noise theorem. Only its statement/introductory hypotheses were read here; its complete dependent arm-estimate proof was not. Accordingly this report does **not** claim an independently paid crossing-circuit theorem or use that statement as a premise for a nomination. Equation (C), with its precise missing target autocorrelation estimate, is the completed lower-bound interface.

### 5.5 Exact obstruction to a tempting third route

Even simple bounded-degree high-temperature input laws cannot be transferred from uniform input by a dimension-free density comparison. On n/2 disjoint edges at zero field and fixed coupling beta>0, set t=tanh beta. Relative to uniform input,

`rho(sigma)=product_pairs(1+t sigma_i sigma_j)`,
`E_uniform rho^2=(1+t^2)^(n/2)`, `||rho||_infinity=(1+t)^(n/2)`.

Both grow exponentially for fixed t>0, including t<1/2. A Cauchy–Schwarz density transfer therefore loses an exponential factor. This is an exact obstruction to that method, not to (A) or (B). Coloring and the posterior edge comparison avoid this loss. In particular a mixture representation without (G) would leave the central physical-noise interface unpaid.

## 6. Current primary comparison and contribution decision

Primary versions were checked in the live searches; raw responses, PDFs and derived text are retained with hashes. The bounds above depend mathematically on the stipulated localization operation and elementary finite-dimensional probability; external results are comparators, not automatic axioms.

Gretta–Gupta–Joshi v2 (August 25, 2026), *Parity not in QAC0 iff QAC0 is Fourier-Concentrated*, was read through the complete relied-upon Fourier/parity reductions and ensuing lower-bound arguments, including majority, felinity, Dicke and the later majority upper construction. Its parametric Quantum-LMN/parity equivalence and high-average-accuracy majority consequence already go beyond a bare worst-case obstruction. The pinned family 274 explicitly supplies these full scalar Fourier operations. Their reuse is charged here; a noise restatement under uniform or product inputs is not a new substantial finding. [Primary v2](https://arxiv.org/abs/2604.02793v2).

Joshi–Tal–Vasconcelos–Wright v4 (August 25, 2026), *Improved Lower Bounds for QAC0*, was read at its strongest statements and complete Section 5 depth-two Fourier proof through its lemma endings. Its logarithmic total-influence and explicit tail bounds are stronger quantitatively at depth two and permit arbitrary ancillas, whereas T1 is qualitative at each fixed depth with polynomially many total qubits. Neither dependence may be silently exchanged. We do not rely on a printed intermediate lemma's norm exponent where its proof displays a different exponent; that literal discrepancy is retained, not silently repaired into a premise. [Primary v4](https://arxiv.org/abs/2512.14643v4).

The Gaussian-mixture comparator v2 of March 15, 2026 was read at its factorization, sampling framework, mixing scope and Appendix A/C derivations through their endings. Diagonal shifting, positive-semidefinite Gaussian augmentation and conditional independent spins are already standard complete operations. Bauerschmidt–Dagallier's full near-critical Ising proof was also read: it decomposes entropy into product and continuous parts and uses a Polchinski/log-Sobolev argument with ferromagnetic correlation input. Its displayed spin-flip Dirichlet normalization is not the heat-bath conditional-variance form used here; with arbitrary fields those forms cannot be identified uniformly. The direct ratio r_a(b) above explicitly pays the comparison needed for our dynamics. We make no claim that Gaussian augmentation, conditional variance decomposition or this elementary comparison is a previously unknown general principle. [Gaussian comparator](https://arxiv.org/abs/2110.10801v2), [Bauerschmidt–Dagallier](https://api.repository.cam.ac.uk/server/api/core/bitstreams/0e495e74-a323-4721-89e8-1753fcaf7738/content).

For T2 the current primary transitive-pointer construction and Bansal–Sinha distinguish total/partial and D/R/Q exactly as described above. We did not rerun their lower-bound proofs as experiments or promote their statements into a new transitive theorem. For T3 the primary WSC and symmetric-circuit papers constrain the permitted model interfaces. [Transitive functions](https://arxiv.org/abs/2103.12355v7), [Bansal–Sinha v3](https://arxiv.org/abs/2008.07003v3), [Lichter–Schweitzer](https://arxiv.org/abs/2205.14003), [Pago](https://arxiv.org/abs/2302.05426). The crossing lead is separately retained without a complete-proof claim. [Tassion–Vanneuville v2](https://arxiv.org/abs/2505.11457v2).

The bounded searches returned many circuit-noise, sampling and fanout papers in different gate/output models. None licenses adding their gates or advice to this circuit model. Search absence is not a priority argument. No worldwide-priority, human/formal certification or invented open-problem ranking is claimed.

**Decision:** (P) is a close extension of the full localization operation; (A) is conditional product analysis; (G) is an explicit additional physical-edge comparison and (B) combines it with (P). Together they provide a useful correlated-input technical theorem beyond merely quoting the uniform parity Fourier tail. The assembly does not establish a substantial ninth contribution under the requested bar. Preserve the exact estimates and PARK stronger circuit lower bounds pending a fully paid target autocorrelation estimate and a separate contribution assessment. T2 lacks a totality-preserving transitive construction with the quartic budgets. T3 lacks a growing-stabilizer support/homogeneity estimate. No incompatible-model synthesis is forced.

## 7. Evidence, finite checks and replay

The package uses the original 13,223-entry tree, 749 manuscript roots, 10,373-original-position map and all 776 PDF/text bindings by reference. The flat reference union preserves the eleven inherited package seals and finalized receipts. A replay traverses the original map once, checks original Git identities and retained text bytes, and executes no ancestor verifier, diagnostic, PDF extraction or numerical search. There is no corpus copy.

Read records bind strict UTF-8, zero-based half-open character ranges, exact hashes and actual endings, raw LF counts, splitlines counts and terminal-LF flags. These are distinct conventions: PDF form feeds are not LF lines. Lexical results retain exact repeated matches, one-based splitlines and zero-based offsets; no Unicode normalization or stemming is silently applied. Corpus coverage, selected lexical domains and semantic reading are different claims. Complete decoded contexts are checked against the original raw records, not reconstructed from live ledgers. Primary PDF/text bindings retain the extraction command and derived hashes; replay checks bytes without rerunning the converter. Failed/truncated retrieval/display attempts and unused preparation products are recorded honestly.

New finite checks use exact rational arithmetic for the phase-average/Fourier identity, biased-product Dirichlet identity, conditional color-class energy and the matching-density obstruction; they also check the exact original ring derivative and safe consumption count. These finite checks do not certify universal circuit localization, universal dynamics, asymptotics, contribution, Gaussian integrals or the literature. The analytic proofs above carry those obligations.

Prevalidation precedes one final seal of the canonically sorted exact owned file/directory inventory. Default verification is offline and read-only, checks all immutable bytes before new diagnostics, disables bytecode and blocks network, subprocess and filesystem mutations. It has no repair or reseal mode. Run from the research root:

```sh
python3 -B frontier/experiments/i147_computational_lower_bound_discovery/verify.py
```

Only the three assigned I147 paths were edited. No shared ledger was updated. A PASS receipt is an integrity and finite-calculation result, not universal mathematical or contribution certification.
