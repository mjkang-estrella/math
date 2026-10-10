# I39 — Quantum/spin and spectral-probability discovery

**Disposition: developed gap record; no substantial finding nominated.** The selected target is a gap uniform in the length and in every sufficiently small scalar bond disorder of the spin-one Heisenberg ring. Two genuinely different approaches are developed below. Neither supplies the missing uniform estimate. The target is **unproved and not refuted**. The complete elementary deductions and obstruction examples in this record are technical, and are not offered as extra findings.

The operative brief reports six accepted findings, including R012, and assigns acceptance, independent reviews, commits and publication to the parent. The initially frozen ledgers still describe five and pending I38 significance; this is historical ledger lag, not an alternative count. No ledger or finding designation was changed. All upstream theorems **and their proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Nothing below audits their truth.

## 1. Scope, prior screens, and source contracts

The [full brief](../sources/i39_quantum_spectral_discovery/full-brief.txt), initial project records and gate reviews are frozen. In particular I read I38's full final significance review, R011's final significance review, and the I30/I36 operation-level reductions. The applicable distinction is an unpaid mathematical operation, not the absence of an identical theorem statement. R012's uniform extra-label activation mechanism is excluded. F007's block-spin tails, response and structure-factor deductions are excluded. I17's distinct-temperature low-temperature free-energy problem is different from the dynamical questions here and is not reopened. The parked I23/I26/I29/I31/I35/I37 routes are not duplicated.

A fresh project search covers **158 Markdown reports/indexes** outside source and experiment caches, including the original `proposals/probability_dynamics.md` and `reviews/haldane-r1.md`, not just frontier reports. There are 15 matched documents under the recorded broad pattern. Some hits are incidental. The exact list and contexts are in `project-search-complete.json`; its two mutable-ledger hits use separately bound later snapshots because the parent updated those ledgers between the initial history freeze and this search. Neither initial snapshot was replaced. These are search coverage numbers, not a claim of reading every report in full.

The entire reused text corpus was SHA-256 and Git-blob checked against the nontruncated tree: **9,340 files, 141,349,121 bytes, 13,223 tree entries, 749 manuscripts**. Both the broad screen and a second targeted stability/LSI/waiting-time screen are retained. The 719-entry contents catalogue is orientation only. Selected proof files are identified by full pinned raw URL, Git blob, SHA-256 and byte count in `selected-pinned.json`. Read ranges and exact statement contracts are separately recorded; collecting a manuscript is not represented as reading all of it.

The main interfaces are:

* **HP:** *The periodic spin-one Haldane gap*, `build/introduction.tex`, `thm:main`, and `assembly.tex`, `cor:local-limit`. In coupling-one units, even rings have a unique ground state for L≥60, and gap greater than δ=log(20)/784 for every even L≥2304. Every local subsequential limit satisfies the local excitation-gap inequality. The source expressly does not identify different limits or prove uniqueness among all infinite-chain ground states.
* **HP operations:** `transfer.tex`, `prop:transfer`, expresses the partition functions as powers of one compact self-adjoint spatial operator. `bootstrap.tex`, `lem:purity`, `lem:rounded-update`, `prop:bootstrap`, uses nonnegative even spectral moments, two-temperature cancellation, quadratic purity improvement, and interpolation of powers of the **same** eigenvalue list. These entire transfer/bootstrap proofs were read.
* **HB:** *A boundary-field gap for the spin-one Heisenberg chain*, `build/main.tex`, `thm:main`, `sections/conclusion.tex`, and `sections/topology.tex`, `cor:topology`. For H_m(h)=Σ_{j=-m}^{m-1}S_j·S_{j+1}−h(S^z_{-m}+S^z_m), h=3/5, m≥960, the ground state is unique and the gap exceeds γ=log(10)/392. Every boundary-selected subsequential state has the stated U(1)/reflection symmetries, local gap and twist index −1. Neither full-chain uniqueness nor automatic identification with a periodic limit is supplied. The boundary residual and signed-pairing operations were also read.
* **SG:** *A spectral gap throughout the high-temperature Sherrington–Kirkpatrick phase*, `sections/introduction.tex`, `thm:main`. For each fixed 0<β<1, Gaussian off-diagonal J_ij of variance β²/n, zero field, and rate-one refresh at each site, Var_μ(f)≤C_β D_μ(f), simultaneously for all f on one event of probability tending to one. D_μ(f)=Σ_i μ Var_i(f). Its actual `observation.tex` proof, not just its title, uses stopped variance retention and control of the bad observation event after square reweighting.
* **SC:** *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase*, `sections/09-cutoff.tex`, `thm:cutoff-continuous`. Worst-start total-variation cutoff at log n/(2λ(β)) is already supplied. Its proof restarts fixed blocks, controls backward gradients, and uses late-time field tails and cube oscillation. It is not merely a gap-to-log(1/π_min) argument.
* **QU/FU:** *Universality of critical quench autocorrelations* and *Functional universality of critical SK autocorrelations*. QU `thm:main` gives the joint compact-positive-time law for Gaussian and Rademacher disorder and relaxation of the **limiting** quench. QU `thm:warming` additionally gives tight L¹→L∞ kernel bounds at each positive critical time, uniformly over disorder-dependent initial laws, **for Gaussian disorder**. Its Gaussian subsequence proof uses weak density/strong cylinder-semigroup pairings. FU `sections/09-functional.tex` supplies a nonnegative spectral-measure representation and decay of the stationary limit.

Current primary papers were searched before choosing the target. Ten versioned primary PDFs and their current-version pages were fetched; eight fresh pinned raw responses agree with the reused source bytes. There were no HTTP failures in these 28 direct requests. The comparisons below distinguish current proof operations from abstracts and search snippets.

## 2. Broad screen: four precise targets

### A. Uniform small bond disorder in the Haldane ring — selected

For self-adjoint spin-one matrices with Σ_α(S^α)²=2I, set

H_L(a)=Σ_{j∈Z/LZ} a_j h_j,   h_j=S_j·S_{j+1}.

**Target H:** there exist ε₀>0 and δ₀>0 such that, for every even L≥2304 and every real vector a with max_j|a_j−1|≤ε₀, H_L(a) has a simple ground eigenvalue and E_1−E_0≥δ₀. Energies are counted with multiplicity. Constants are independent of the deterministic disorder profile, its period and its length. There is no probabilistic averaging, no bond of strength zero, and no assertion about odd rings, free open boundaries, all infinite-chain ground states or string order. Taking ε₀<1 keeps every bond antiferromagnetic.

The named problem is robustness of the Haldane gapped phase to weak exchange disorder. Its physical and mathematical motivation is explicit in the stability literature and Tasaki's separation of gap and topological hypotheses. The reason it survives the initial screen is concrete: HP pays uniform homogeneous spectral concentration, whereas arbitrary words of perturbed spatial operators and uniform relative-energy control remain unprovided. Constant rescaling and bounded-total-strength defects, proved below, are technical special cases.

Endpoint tests: a_j≡a>0 simply rescales the gap, so a proposed method should not charge L|a−1| in this case. Allowing a bond to vanish moves toward open-chain edge issues and lies outside H. A boundary-field gap cannot be substituted for an unfielded open-chain gap. Adiabatic continuation along a path already known gapped would preserve structural data but would not prove H.

### B. Classical heat-bath LSI throughout β<1 — not selected

**Target S:** for every fixed 0<β<1, there is C_β<∞ such that with probability tending to one over the same zero-field Gaussian disorder as SG,

Ent_μ(f²)≤C_β Σ_i μ Var_i(f)  for every real f.

Entropy uses natural logarithms; each site has a rate-one clock. For the uniform-site-attempt chain the right form is D/n and its LSI constant scales as n. This is **classical** LSI, not the modified inequality Ent(z)≤C D(z,log z), and not a fixed-initial-law mixing statement. At β=0 the product inequality provides the expected finite constant; no uniformity as β↑1 is requested.

SG's complete observation transfer only needs normalized f with D(f)≤1. Its square-tilted observation entropy satisfies an estimate of the form H_τ/n≤Cδ+C_δ(2+D(f))/√n. Since the bad path probability is e^{-cn}, this makes the bad **mass** small. It does not bound the bad **entropy contribution** in proportion to D(f), which is the new obligation for S. A candidate entropy-retention transfer would have to pay that contribution uniformly over all square tilts, not replace it by o(n).

The stronger current comparison is [Wang, 2608.22159v2](https://arxiv.org/abs/2608.22159v2), Theorems 4.1–4.3 and their proofs. An all-external-fields covariance bound, simultaneously for the rescaled interactions sJ, yields modified LSI; its β<1/2 result is uniform in external field. SG's zero-field theorem plus its restricted random-posterior estimates does not supply that all-field hypothesis. Also D(f²,log f²)≥4D(f), so a bound by the former cannot be reversed into the desired classical LSI. This is a material distinction, not an omitted constant.

[Boban–Li–Oveis Gharan, 2609.13138v1](https://arxiv.org/abs/2609.13138v1), Proposition 1.4 and Theorem 1.5, use a rank-one-shifted integrated curvature estimate to obtain a gap up to β<1/2+ε. The actual summation is quadratic in the test derivatives. [Davies–Lee–Sandhu–Shi, 2607.08160v1](https://arxiv.org/abs/2607.08160v1), Theorem 1.4/Corollary 1.5, instead transfers weak Poincaré control with an error term. [Bandeira–El Alaoui–Rödder, 2607.06813v1](https://arxiv.org/abs/2607.06813v1), Theorem 1.1/Corollary 1.2, require a sufficiently large external field for their high-overlap route. None of these inspected operations closes S. This is a bounded comparison, not an assertion that the entire LSI literature was exhausted.

A simple interface countermodel is the two-state refresh chain with stationary masses p,1−p and generator Pf−f, Pf=μf. Its gap is exactly one, but for f=1_{rare}/√p,

Ent(f²)=log(1/p),   D(f)=1−p.

The classical LSI constant diverges. This is not zero-field SK and is not a counterexample to S. It proves why the generic Poincaré implication cannot be used. SC's already-proved cutoff is rejected as a duplicate target, and the crude gap/log-atom mixing estimate is rejected as technical. S remains an entropy-transfer gap, less concretely accessible here than H.

### C. Uniform finite-size critical waiting-time relaxation — not selected

Use QU's exact definitions at β=1, T_n=n^{2/3}, ν_n the independent fair-spin law, and rate-one clocks at every site:

A_n(t)=n^{-2/3}Σ_i〈σ_i,P_{tT_n}σ_i〉_π,
B_n(s,t)=n^{-2/3}Σ_i E_{ν_n}[σ_i(sT_n)σ_i((s+t)T_n)].

All thermal randomness is averaged; only disorder remains random. **Target W:** for both Gaussian and Rademacher couplings, every 0<a<b<∞ and η>0,

lim_{S→∞} limsup_{n→∞} P_J{sup_{s≥S, a≤t≤b}|B_n(s,t)−A_n(t)|>η}=0.

This asks for finite-size waiting times that can escape every compact set. QU's source conclusion instead takes the limit n→∞ on compacts first and then lets s→∞ in B_g. The distinction concerns the actual order of limits in critical relaxation/aging, a motivation explicitly discussed in QU's introduction. No worst-start conclusion or claim at t=0 is included; A_n(0)=n^{1/3}, so the positive-lag restriction is essential.

A sufficient new input would be a tight **low-energy compactness estimate for the evolved densities and the correlation tests**, strong enough to prevent mass in unresolved slow modes and to transfer to Rademacher disorder. Gaussian warming supplies bounded densities and kernels, but the stated subsequence proof has weak, not norm-preserving, convergence for those densities. The source's finite-horizon entry-replacement bounds have parameters fixed before n, and cannot simply be run to a diverging terminal time. The exact reversible-chain test in §6 shows a genuine problem with a weaker proposed inference. It is not an SK counterexample and does not purport to satisfy the full source's edge-form hypotheses.

The stronger *Critical mixing in the Sherrington–Kirkpatrick model* companion, `introduction.tex`, `thm:main`, already gives Gaussian worst-start mixing, full relaxation and classical LSI constants of order n^{2/3+o(1)}. Its exact statement explicitly retains every fixed positive exponent slack for the full constants; only the linear-observable companion has arbitrary-diverging-factor control. Thus the printed full-constant bound permits a factor diverging with n after division by T_n and does not yield the fixed-S waiting limit in W. This is a quantifier limitation of that interface, not a new lower bound on relaxation.

A weaker uniform **lag** extension for the stationary process is technical and proved in §6: positivity of its spectral measure already pays it. Thus replacing waiting by lag would relax away the missing mechanism and is not a nomination.

### D. PEPS construction/accuracy — early interface rejection

For the open-square class of family 265, a possible algorithmic target is a deterministic procedure that takes rational local interactions, a promised fixed gap Δ and ε∈(0,1), and outputs polynomial-bit PEPS tensors of polynomial bond dimension in time polynomial in L, input bit length and 1/ε, with normalized global vector error ε. This is a precise construction target, not efficient contraction of arbitrary PEPS.

The source already proves polynomial bond dimension for error L^{-1}. Its `sections/04-compression.tex` allows unrestricted private dimensions and vectors; `sections/07-assembly.tex` starts with private copies of the exact unknown Ω and selects a product-basis column by an existence argument, without a lower bound on its overlap. These operations do not yield the proposed input-to-output algorithm. Its angular information, adaptive patch, frame, compression and routing interfaces are all in the collected proof inventory, but this screen stops at the explicit nonalgorithmic interface: it does not claim a full new algorithm audit or a lower bound for this promised class.

Even changing the fixed inverse-polynomial error power is already paid: compression admits every fixed accuracy exponent and the assembly explicitly fixes its error powers first. Naive entropy-to-efficient-description reasoning is contradicted for general area-law states by [Ge–Eisert, 1411.2995v2](https://arxiv.org/abs/1411.2995v2), Theorem 8 and its net-count proof. Their states are not counterexamples to the additional local-gapped-Hamiltonian promise. The stronger algorithmic target needs constructive access to Ω-dependent maps and a stable column/parameter representation; no such mechanism was supplied here. No accuracy-only or generic area-law corollary is nominated.

## 3. Selected route I: disordered spatial histories and purity

Write Z_a(b)=Tr exp[−b H_L(a)], with scalar energy shifts omitted because they cancel in physical purity. HP's Cartesian identity is −h=Σ_αG_α⊗G_α, and its chronological kernel k_b(x,y) has |k_b|≤3. If |x| is the number of events in a bond history, the ordered expansion gives the exact disordered formula

Z_a(b)=∫∏_{j=1}^L k_b(x_{j-1},x_j) ∏_{j=1}^L a_j^{|x_j|} dμ_b(x_1)…dμ_b(x_L),

with x_0=x_L. Absolute convergence follows from the source's expansion with max a_j in place of one. This is a legitimate extension of an accepted proof operation; it is technical.

To avoid an unbounded multiplier, put A=max_j a_j and use the reference history measure dμ_{b,A}=A^{|x|}dμ_b, whose mass is e^{3Ab}. On L²(μ_{b,A}), multiplication by d_j(x)=(a_j/A)^{|x|/2} is a positive contraction. The formula becomes a trace of an alternating product of the common kernel operator and the bounded multipliers d_j². Every needed kernel product is trace class. The individual symmetrized factors d_j K d_j are self-adjoint, but a general product has neither a common spectral resolution nor HP's representation as powers of one self-adjoint operator.

That failure has two concrete consequences.

1. Repeating a word and concatenating a word with a **different** word are different operations. HP's spatial squaring uses the former through a common eigenvalue list. Arbitrary disorder in H permits the latter. No purity inequality controlling all concatenations has been proved.
2. Small coefficient changes do not make the raw multiplication operators uniformly close in operator norm: if 0<a<A, then ||I−(a/A)^{|x|/2}||=1 because every event count has a positive-measure simplex. Integrated Hilbert–Schmidt continuity at each fixed b survives, but a uniform-temperature perturbation margin does not follow from it. This does not prove discontinuity of the physical gap.

For example, with the unweighted history measure, a,c≤A and A≥1,

Σ_{k≥0}(3b)^k/k! · |a^k−c^k|²
≤ |a−c|² e^{3bA²}[(3b)² A²+3b].

Indeed |a^k−c^k|≤k A^{k−1}|a−c| and Σ k²z^k/k!=(z²+z)e^z. Multiplying by the other history mass and the kernel bound gives a finite Hilbert–Schmidt estimate, but its displayed constant grows exponentially in b. HP doubles b with L. No normalization-relative cancellation has been established to remove that growth.

A second attempt compares physical traces directly. If V=H_L(a)−H_L(1), then ||V||≤2Σ_j|a_j−1|≤2εL. Weyl's eigenvalue inequalities imply

e^{-b||V||}Z_1(b)≤Z_a(b)≤e^{b||V||}Z_1(b).

Therefore the physical purity T_a(L,b)=Z_a(2b)/Z_a(b)² satisfies

T_a(L,b)≥e^{-4b||V||} T_1(L,b).

At HP's dyadic pairs n_j=2304·2^j, b_j=784·2^j, u_j=(1/5)(1/20)^{2^j}, and n_j≤L≤2n_j, the source supplies T_1(L,b_j)≥1−3u_j. The resulting estimate is only

1−T_a(L,b_j)≤1−e^{-8εb_j L}(1−3u_j).

The comparison cost is order εL² before it saturates. Keeping this estimate above 1/2 alone requires an L-dependent perturbation scale; retaining HP's exponentially small defect for a fixed gap is more demanding still. The defect recurrence cannot absorb a fixed additive perturbation while u_j decays doubly exponentially in j. These are failures of these sufficient estimates, not examples of a closing Heisenberg gap.

**Missing operation on route I:** a disordered replacement for homogeneous spatial squaring, with an error measured relative to the contracting residual weight and summable through temperature/length doubling, uniformly over arbitrary concatenated coefficient words. A fixed-temperature analytic-continuity statement or a common-period proof with constants deteriorating in the period does not meet H. No such replacement is proved here.

## 4. Selected route II: local energy, dressing, and positive constraints

This route does not use transfer products. It tries to compare perturbed excitations to the original energy above the ground state.

### 4.1 Why the raw positive-bond comparison does not work

Each h_j has eigenvalues −2,−1,1, so k_j=h_j+2I≥0. Set K_0=H_L(1)+2LI. For |a_j−1|≤ε,

(1−ε)K_0≤Σ_j a_j k_j≤(1+ε)K_0.

The scalar shift −2Σ_j a_j does not change the perturbed gap. Min–max thus gives the lower bound

gap H_L(a)≥(1−ε)gap H_L(1)−2ε E_0(K_0).

HP's actual three-site energy inequality h_{12}+h_{23}≥−3I yields E_0(K_0)≥L/2. Thus the unremoved frustration energy is extensive. One cannot cancel the two occurrences of E_0(K_0) as if every local k_j annihilated Ω. For the special case a_j≡a the exact answer is a·gap H_L(1), illustrating that this comparison discards a real cancellation rather than disproving robustness.

Nor can one simply center every perturbing bond and bound it by the excitation energy. Here is an obstruction **inside the target's unperturbed Heisenberg family**, for every L divisible by four and L≥2304.

In Cartesian coordinates let A=Σ_{i,j}|i i j j〉 and B=Σ_{i,j}|i j j i〉 on four sites. These are unnormalized products of two singlets. For the open four-site Hamiltonian, direct integer contraction gives

Gram(A,B)=[[9,3],[3,9]],
〈(A,B),H_open(A,B)〉=[[-36,-18],[-18,-18]].

The vector A+B/4 therefore has Rayleigh quotient −246/59<−4. Tiling the ring with normalized copies gives zero expectation on the joining bonds, because each block is a rotational singlet. Hence E_0(H_L)/L≤−123/118<−1. The unique periodic ground state's bond expectation e_L is the same at every site by translation invariance. It is strictly greater than −2: equality would put every neighboring pair in its one-dimensional singlet space, impossible on three sites. For example, a pure state with the first pair a singlet factors that pair from the rest, whereas a second overlapping pair cannot simultaneously be a pure singlet. Consequently −2<e_L<−1, and h_jΩ is not a scalar multiple of Ω, since those are consecutive bond eigenvalues.

For a fixed bond define W=h_j−e_L I, χ=WΩ≠0, and K=H_L−E_0. Then χ⊥Ω and, for ψ_t=Ω+tχ,

〈ψ_t,Wψ_t〉=2t||χ||²+t²〈χ,Wχ〉,
〈ψ_t,Kψ_t〉=t²〈χ,Kχ〉.

No finite C can make |〈ψ,Wψ〉|≤C〈ψ,Kψ〉 hold for all ψ. The linear term defeats the quadratic one as t→0. This is a rigorous obstruction to an **undressed** relative-form lemma, not to H: ordinary perturbation theory changes the ground vector precisely to remove this term. The diagnostic checks the new four-site contraction and triad polynomial with exact rational arithmetic; no large-ring diagonalization is alleged.

### 4.2 What known stability proofs require

[Moon–Nachtergaele, 1804.04750v2](https://arxiv.org/abs/1804.04750v2), §2.2, Theorem 3.11 and its actual proof, assume a nonnegative finite-range frustration-free interaction, uniform **local** gaps and a quantitative LTQO estimate for local ground-space projectors. Lemma 3.5 uses nesting of those projectors; Proposition 3.6 uses it to decompose the dressed perturbation into terms annihilating appropriate local ground spaces; the ensuing relative form bound closes a maximal-gapped-interval argument. These are exactly the operations that must be supplied in a Heisenberg application. The theorem does not take only HP's even-ring global gap as input.

[Michalakis–Zwolak, 1109.1588v3](https://arxiv.org/abs/1109.1588v3), the Local-TQO/local-gap hypotheses and their proof uses, make the same local distinction. Their local reduced-state control concerns ground spaces of restrictions, not just exponential connected correlations in one global state. [De Roeck–Schütz, 1501.04571v2](https://arxiv.org/abs/1501.04571v2), §2.2 and Proposition 3.1/Theorem 3.2, assume a gap along the entire deformation; their constants also see the size of the perturbation region. Iterating that result over all bonds without retaining a uniform gap would be circular.

The current [Tasaki index-equivalence paper, 2609.34119v1](https://arxiv.org/abs/2609.34119v1), Theorem 2.2 and Corollary 2.4, is stronger than an old twist-index citation: it gives an explicit local-twist error and allows nonuniform interactions when its symmetry and gap premises hold. Its Heisenberg application separately assumes infinite-chain uniqueness and the boundary-field gap. It therefore supplies neither missing gap stability nor an identification of HP and HB limits. F007 and HB's existing twist consequence remain spent interfaces.

### 4.3 A distinct attempted repair using the area-law source

The family-265 positive replacement is relevant at the **proof-operation** level even though the selected target is one-dimensional. Embed an even ring of length at least eight as the perimeter of an induced rectangular lattice domain with both side lengths at least three. Its graph is the cycle; there are no extra interior sites. The global-gap/locality construction in the area-law paper, `03-quasilocal.tex`, `prop:positive`, therefore applies with uniform local parameters.

It constructs Hermitian quasi-local M_j such that

M_jΩ=0,   Σ_jM_j=H_L−E_0,

then k_j=|M_j|/c_*∈[0,I], with

H_F=Σ_j k_j ≥ (H_L−E_0)/c_*,   H_FΩ=0,
||k_j−E_{N_r(j)}k_j||≤C exp(−c r^α),  α<1 fixed.

This really does give an exact globally frustration-free quasi-local replacement; it must not be dismissed as merely an area-law statement. But it does not give the following two facts needed by the proposed repair:

* compatible finite-region zero-energy spaces with uniform local gaps and LTQO;
* a uniform **upper** comparison H_F≤C(H_L−E_0), or another estimate that transfers a perturbative excitation bound back in the needed direction to the original Hamiltonian.

The printed domination is in the opposite direction for the latter task. A common-ground-state gapped interpolation between H_L−E_0 and H_F is available, but a gapped path does not by itself assert stability of a whole neighborhood of its initial endpoint.

Truncating the positive constraints does not preserve exact frustration freeness. This problem occurs even with arbitrarily small truncation error. On two qubits put a=(1−t²)/(1+t²), b=2t/(1+t²), 0<t<1, and

Ω=a|00〉−b|11〉,
k=|10〉〈10|+|v〉〈v|,   v=b|00〉+a|11〉.

Then k is a positive projection and kΩ=0. The normalized conditional expectation onto the first qubit is

E_1(k)=diag(b²/2,(1+a²)/2)⊗I.

It is strictly positive, hence has no zero-energy space. Direct diagonalization of two 2×2 blocks gives

||k−E_1(k)||²=b²(1−3b²/4)≤b²→0.

Thus small norm error is not an exact-kernel statement. This two-qubit example is not claimed to be HP's particular filtered constraint. It disproves the generic truncation inference that the repair would otherwise need. Taking r of order (log L)^{1/α} makes the **total** norm error small, but produces a volume-dependent range and still does not supply local kernels/LTQO. No bound uniform in L has been extracted by this method.

### 4.4 A precise sufficient missing lemma

A convenient way to state the remaining energy obligation is **RF**. Let K_L=H_L(1)−E_0, η_j∈[−1,1], and H_L(s)=H_L(1)+sεΣ_jη_j h_j. On every initial interval where the ground eigenvalue is simple and its gap is at least δ/2, construct unitaries U_s mapping Ω_0 to Ω_s. RF asks for a constant C, independent of L, η and that interval, such that

D_s=U_s^*(H_L(s)−E_0(s))U_s−K_L,
|〈ψ,D_sψ〉|≤C sε〈ψ,K_Lψ〉  for every ψ.

The ground projection is fixed after conjugation, so no linear ground/excited cross term remains. If RF held, choose ε<1/(2C). On a maximal interval with gap at least δ/2, min–max would give gap≥(1−Cε)δ>δ/2, contradicting a first exit. Finite-dimensional continuity would then give H with a uniform positive threshold. This is a sufficient formulation of the missing work, not a claim that RF follows from HP or that it is equivalent to the weakest possible robustness theorem. The local-projector mechanism of Moon–Nachtergaele explains one way to establish it under extra structure; that structure remains unpaid here.

## 5. Complete technical perturbation deductions

These facts are retained for precise scope, not nominated.

For any a>0 and η_j∈R, write H'=aH_L(1)+Σ_jη_jh_j. Weyl gives

gap H'≥aδ−4Σ_j|η_j|   (even L≥2304),

whenever the right side is positive. It also ensures simplicity. One can optimize over the common scaling a; constant rescaling costs nothing beyond the factor a. This covers finitely many defects with bounded total strength, or an ℓ¹ perturbation family uniformly in L. It does not cover all ℓ∞-small disorder, since Σ|η_j| can grow with L. No thermodynamic uniqueness assertion is attached.

Likewise, for the same-field odd open chain and h₀=3/5,

gap H_m(h)≥γ−4|h−h₀|.

Hence |h−h₀|≤γ/8 gives a uniform gap at least γ/2 for all m≥960. The field remains positive. The exact hypotheses of Tasaki's boundary-field theorem remain satisfied, so every boundary-selected subsequential limit has twist index −1. This interval extension is Weyl plus the already-used Tasaki operation; it is **technical only**. Unequal endpoint fields can be treated by a norm estimate but would not automatically retain the reflection hypothesis used in the cited index argument.

## 6. Additional exact checks on the spectral screen

### Stationary large lags: a technical consequence

FU writes A_n(t)=∫e^{-tλ}dν_n(λ) with ν_n nonnegative, and proves A_g(t)→0 as t→∞. For each n, A_n is nonnegative and decreasing. Therefore, for any η>0,

lim_{T→∞} limsup_n P{sup_{t≥T}A_n(t)>η}=0.

Indeed the supremum is A_n(T); weak convergence at each fixed T and the Portmanteau bound reduce the limsup to P{A_g(T)≥η}, which tends to zero. Together with compact convergence, this yields stationary convergence in the uniform-on-[a,∞) topology for each a>0 (with vanishing-at-infinity functions). A usual truncation at T proves tightness and identifies the limit. This applies to both disorder laws. It uses the source's positivity/decay directly and does not pay the waiting-time requirement W.

### A reversible delayed-bump test

Here is an exact finite-state obstruction to the suggested inference “compact convergence plus relaxation of the limit plus bounded evolved densities implies W.” It does not satisfy all SK source hypotheses, and is not a counterexample to W.

On {−1,1}³ use independent reversible coordinate-flip chains for x,y,z, with decay eigenvalues 1/N,2/N,1. Thus their flip rates are half these values and the invariant law π is uniform. Start from density h_0=1+α(x−y), α=1/4, relative to π. It is a probability density in [1/2,3/2]. At time s,

h_s=1+αe^{-s/N}x−αe^{-2s/N}y,

so those same bounds hold for all s≥0. The observable f=z(1+x+y)/3 has |f|≤1 and πf=0. Direct product-semigroup calculation gives

A_N(t)=e^{-t}(1+e^{-t/N}+e^{-2t/N})/9,
B_N(s,t)−A_N(t)=αe^{-t}/9 · [(1+e^{-t/N})e^{-s/N}−(1+e^{-2t/N})e^{-2s/N}].

Both functions converge on compact positive-time sets to A(t)=B(s,t)=e^{-t}/3. The limiting quench is stationary and decays in lag. For every finite N the chain eventually relaxes. But at s=N log2 and any fixed t>0,

B_N(N log2,t)−A_N(t)→e^{-t}/72>0.

Consequently the desired supremum over late waiting times cannot be inferred from just those properties. The calculation is verified on the actual eight-state product kernels at 27 rational attenuation triples; it is not a free choice of arbitrary continuous functions. A low-energy compactness or uniform-relaxation input excluding such hidden modes is substantive. The Gaussian warming bound alone does not exclude this example: its finite state space even has a uniformly bounded kernel. This observation does not assess whether the **other** detailed edge estimates in QU can eventually supply the required missing input.

## 7. Evidence and limits

The source corpus and all prior artifacts were read-only to this task. During parent integration, the live R012 finding record lost one trailing newline and two shared ledgers changed. The original snapshots remain untouched; `observed-live-drift.json` binds the exact R012 change separately, without refreshing any dependency. No agents were spawned, no shared file was edited, and no staging, commit, push or publication was performed. No previous seal was refreshed. The evidence package records:

* the full brief, frozen controls/history and a manifest distinguishing mutable ledgers from immutable dependencies;
* both complete-inventory corpus search passes, full corpus hash checks, the project-report search, selected pinned identities and eight fresh identical raw responses;
* four retained web request/response snapshots, ten primary version pages, ten corresponding versioned PDFs/texts, all response metadata, and visual checks of Moon–Nachtergaele's actual local assumptions and Tasaki's local-versus-global uniqueness distinction;
* actual read ranges, theorem/operation contracts, an exact diagnostic program, and a one-time artifact seal.

All 28 HTTP responses succeeded. Two optional local parsing/algebra imports (`bs4`, `sympy`) were unavailable; they were replaced with standard-library parsing and exact `Fraction` arithmetic. Those failures and the PDF font warnings are recorded, not suppressed. There are **389 exact assertions** in the diagnostic program: four-site contraction, the triad's annihilating polynomial, arbitrarily small twirl/kernel-loss examples, reversible-chain identities, purity bookkeeping, and rare-atom normalization. No floating output is used and no numerical diagonalization is offered as proof. These finite diagnostics do not certify the universal proposed targets or establish novelty.

Read coverage is intentionally honest: complete HP transfer/bootstrap and the decisive HB boundary/conclusion/topology proofs; the full positive-replacement construction; SG's observation transfer and posterior interfaces; QU's warming statement and the relevant Gaussian-subsequence proof passages; FU's spectral continuity/decay proof; the cutoff assembly interfaces; and the PEPS representation/compression/assembly contracts. The entire corpus was searched, not semantically read. No claim of a complete global PEPS algorithm audit or exhaustive worldwide literature search is made. The PEPS screen was rejected early, so it is not a substitute for one of the three fully specified H/S/W targets.

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```bash
python -B frontier/experiments/i39_quantum_spectral_discovery/check.py
python -B frontier/experiments/i39_quantum_spectral_discovery/verify.py
```

The verifier rehashes all 9,340 corpus files and reproduces both corpus searches, checks the retained responses/pins/read ranges/frozen inputs/seal, and reruns the exact diagnostics in memory. It writes no files and reports live mutable-ledger drift separately. The acquisition/packaging scripts are one-time tools and must not be rerun to refresh sealed evidence.

**Final verdict:** H remains unproved and not refuted after transfer-purity and local-energy/positive-replacement attempts. S and W retain explicit missing mechanisms. The elementary partial results and scoped counterexamples are technical. No result is ready to count or publish as a new substantial finding; the parent may review this developed gap record without treating a failed sufficient bound as a target counterexample.
