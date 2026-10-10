# I85 — original-proof review of C80

**C80: ORIGINAL PASS WITHOUT REPAIRS**, relative to the stipulated pinned corpus. This verdict concerns the original author report, SHA-256 `a849a5d273fcfc3a01fe6d0391209e4e8f3e0e665612077e7899203bac78c0e2`, not a revised construction. I found no substantive mathematical repair necessary. The additional calculations below expose the checks behind that verdict; they do not replace a missing gate or change its parameters.

**Nomination remains HELD.** This is an independent original-proof review, not a contribution or novelty verdict, acceptance, publication, or count change. Eight substantial findings remain accepted. The original broad I80 assignment is not fully discharged. A separate independent contribution round remains required. G, R, and arbitrary-core infinite completion are not nominated here.

| Original assertion | Verdict | Scope |
|---|---|---|
| Lemma 3.1, harmonic pressure criterion | ORIGINAL PASS WITHOUT REPAIRS | Every harmonic degree; smooth compact velocity |
| Lemma 3.2, radial swirl identity and pressure evaluation | ORIGINAL PASS WITHOUT REPAIRS | Translated centers, all harmonic polynomials, correct sign |
| Lemma 3.3, balanced rotation gate | ORIGINAL PASS WITHOUT REPAIRS | Disjoint concentric shells, equal positive moments, orthonormal axes |
| Section 5, small-angle translation and derivative estimates | ORIGINAL PASS WITHOUT REPAIRS | The stated axes, ordered pulses, every intermediate time |
| Section 6 loading | ORIGINAL PASS WITHOUT REPAIRS | Includes rational zero loading scale; no false detector crossing |
| Section 6 global compiler and C80 | ORIGINAL PASS WITHOUT REPAIRS | All six original conclusions, with the exact RV comparison class |
| Lemma 4.1, finite harmonic-moment completion | ORIGINAL PASS WITHOUT REPAIRS | Finite N, effective supplied data; **unused by C80** |
| Six-center fourth-harmonic example | COUNTEREXAMPLE, confirmed as written | Refutes sufficiency of quadratic isotropy/cubic stress symmetry; **unused by C80** |
| Arbitrary-core infinite completion | GAP / OPEN, as explicitly acknowledged by I80 | No uniform smooth/effective infinite completion established; **unused by C80** |

No typo correction is needed to obtain these verdicts. “Constant plus a harmonic quadratic” near the center in Lemma 3.2 is a permissible description: for these profiles the quadratic coefficient is actually zero. “Cubic symmetry” in the counterexample is used at the quadratic-stress/moment level; the counterexample does not need the signed velocity itself to be equivariant under every cubic rotation. Neither observation is a substantive repair.

## Original inputs and reading scope

The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All pinned statements and lower proof operations are true premises. I audit their applicability and the new deductions, without exploiting purported upstream inconsistencies. No external fluid construction is a premise of this verdict.

The complete original assignment, author findings, unresolved limitations and finalized parent response are retained verbatim in [full-brief.txt](../sources/i85_compact_solenoidal_computation_r2/full-brief.txt), extracted from the immutable I85 task record. The original report, I80's 96-file seal, original verifier and finalized parent wrapper are immutable references. They were not modified or resealed. [inputs.json](../sources/i85_compact_solenoidal_computation_r2/inputs.json) binds frozen copies of AGENTS, the task, tree/catalogue inputs and four ledgers. Only the four live ledgers have informational drift treatment; their frozen copies do not.

[Source manifest](../sources/i85_compact_solenoidal_computation_r2/source-manifest.json) records exact paths, Git blobs, SHA-256 hashes and pinned raw URLs. [Passages](../sources/i85_compact_solenoidal_computation_r2/passages.json) records actual semantic reading by byte-line ranges and fragment hashes. [Coverage](../sources/i85_compact_solenoidal_computation_r2/read-coverage.json) explicitly lists unbound ranges. A hash, search hit, PDF extraction, or equal-version comparison is not credited as semantic reading.

The following complete mathematical bodies were read, including their included proof files:

- RV: `build/main.tex` 1–312, `addressed.tex` 1–396, `alternating.tex` 1–276, `lattice.tex` 1–383. The direct dependency is the addressed construction; the other implementations were checked for scope, not substituted for it.
- ES: `build/main.tex` 1–1017.
- VD: `build/main.tex` 1–288, `compact.tex` 1–437, `bounded.tex` 1–618, including the detector proofs.
- SP: `main.tex` 1–82 and all its mathematical included files: `analytic` 1–41, `main-result` 1–15, `bcs-clocks` 1–48, `bcs-clock-options` 1–42, `bcs-scalar` 1–139, `bcs-prefix` 1–125, `bcs-expanded` 1–283, `scalar-stages` 1–21.
- GS: `main` 1–35, `introduction` 1–208, `analytic-imports` 1–82, `body` 1–1418, `reciprocal-template` 1–94, `clocks` 1–83, `recorder-import` 1–38, `interpreter` 1–88, `normal-figure` 1–31.
- FS: `build/main.tex` 1–1012.
- FP: `build/main.tex` 1–663, `analytic-tools.tex` 1–109, and **the actual analytic appendix** 1–129.

For both IB versions I read the complete analytic and clock files: September `analysis.tex` 1–208 and `clocks.tex` 1–122; October `analysis.tex` 1–282 and `clocks.tex` 1–140. For October I also read `main` 1–56, `introduction` 1–173, `geometry` 1–324, `balanced` 1–166, `compact-processors` 1–189, `compilers` 1–307, `routing-conventions` 1–255 and `solid-routing` 1–668. Additional exact ranges in `guarded-history`, `initialization`, `observer-routing`, and `persistent-history` check the alternative force and comparison contracts. These ranges, including stronger pressure classes, are in the passage ledger. The 17 same-name build-file version comparisons retain the three changed files (analysis, clocks, main) separately from the 14 identical files. Identical files were not falsely recorded as a second semantic reading.

For PI I read `main` 1–56, `introduction` 1–154, `principal-theorem` 1–11, `analysis` 1–204, `full-boxes` 1–152, `sheet-geometry` 1–220, `compact-reciprocal` 1–210, `autonomous` 1–338 and `prefix-realizations` 1–676. In `planes-and-histories` I read 1–80, 301–337, 388–455, 789–888 and 960–1083: the planar/lift operation and the actual Euclidean, torus-projection and decay contracts and proofs.

This completes the prerequisite and relevant fluid-interface reading for the **scoped C80 proof verdict**. It does not assert full reading of every alternative IB/PI symbolic compiler or routing implementation. Those unused ranges, bibliographies, duplicate-version bodies and unrelated geometric manuscripts remain visibly unbound. In particular it does not discharge I80's stronger original all-companion contribution-reading assignment. No deduction here relies on an unread alternative symbolic table. The source statements/operations actually imported into C80 are the fully read RV ones and FP's underlying comparison proof.

## Exact source contracts

RV `addressed.tex` 44–155 supplies the finite configuration codes, padded all-address functions, the range bound, the **same** scales used by I80, total-memory bound and divisibility/read operation. In particular, its convention sets F_n=0 outside the lookup case, including terminal codes. Invalid unscanned padded digits do not invalidate its range bound. Its estimates and effectiveness discussion occur in 218–331. These are inputs; I do not replace their quantifiers or independently audit their truth.

RV `main.tex` 150–208 defines the classical Euclidean class and Lemma `lem:realization`. It explicitly covers an independently established reference pair (U,P), including nonzero pressure, and permits omission of the competitor's gradient bound while retaining bounded competitor velocity and all Sobolev/pressure conditions. FP `analytic-appendix.tex` 8–111 supplies that exact noncompact cutoff comparison, not merely the pressure-zero substitution. RV `main.tex` 209–238 is a **periodic** projection theorem and explicitly supplies no Euclidean compact-support preservation. Its effective-profile discussion and FP `main.tex` 530–589 avoid equality tests at flat joins. The complete files, not only these highlighted ranges, were read.

The companion scope checks agree with the following bounded statements:

| Family | Actual available operation | Restriction relevant to C80 |
|---|---|---|
| RV | Unit-time all-address computation; all fixed rapid mixed bounds; finite particle length | Original Euclidean residual is general, with pressure zero; projected version is toroidal |
| ES | Eventually steady/periodic forcing and an onto slow clock | Fixed torus; projection changes pressure; an integrable clock cannot traverse all internal time |
| VD | Fixed positive velocity thresholds | Compact-torus short bursts cost time derivatives; expanding-array construction lacks one fixed spatial support |
| SP | Compact general forcing and logarithmic-clock decay, scalar potentials and invariant planes | Inverse-time decay is not arbitrary rapid decay; compact localization does not assert solenoidal residual |
| IB, both versions | Full-box/guarded transport, effective clocks, several uniqueness classes | General compact residuals have pressure zero; solenoidal projection assertions are on tori |
| GS, FS | Direct solenoidal forcing from time-separated transverse shears | A flat torus; dependent-coordinate cutoffs do not make a nonzero shear compact in its direction of travel in R3 |
| PI | Boxes, compensated sheets, invariant planes, compact periodic processors | Explicit general-force contracts; torus projection and slow-clock alternatives remain distinct |
| FP | Exact prescribed-reference uniqueness and effective smooth profiles | Reference and competitor hypotheses, including the selected pressure normalization, must be retained |

Two exact stronger source operations deserve recording without promoting them to a C80 antecedent. IB's `analysis.tex`, Lemma `lem:b-comparison`, case (v), supplies comparison with no separate spatial pressure-integrability hypothesis for the stated bounded velocity/gradient, CH2∩C1L2 class, obtaining an L2 gradient from the equation. `solid-routing.tex` 561–668 uses it in the guarded planar event. Other cases retain CL2 pressure or gradient-only conditions. These are different contracts from C80's selected CH1 pressure class. October IB also sharpens the explicit periodic projection estimates to H^(r+2)-based bounds and a quantitative Fourier tail, with matching clock envelopes; September uses a higher-order sufficient estimate. None asserts the new Euclidean all-moment pressure cancellation. PI's label `rapid-periodic` names compact periodic processors, not rapidly vanishing forcing; its actual statement was read.

## Pressure identities and finite gate

For divergence-free v, div((v·∇)v)=∂i∂j(v_i v_j)=S_v. With G=1/(4π|x|), **−ΔG=δ**, so p=G*S_v satisfies −Δp=S_v. Consequently

`div(v_t+(v·∇)v+∇p−νΔv)=S_v+Δp=0`.

The author's pressure sign is correct. Reversing it would fail the required force condition.

For Lemma 3.1, compact p implies ∫S_v H=∫p(−ΔH)=0; integration by parts gives exactly M_v(H). Conversely the exterior Newtonian expansion pairs S_v with harmonic homogeneous polynomials in the source variable. On |x|≥R+ε its derivatives converge uniformly on the support, so all coefficients vanish. This proves exterior vanishing for every |x|>R without an unjustified limit at |x|=R. Smoothness across that sphere follows from the already smooth convolution, not by cutting off a nonzero tail. Traceless quadratic Hessians give isotropy of ∫v⊗v, and do not alone prove the criterion.

For Lemma 3.2 write v_0=a×y, L=v_0·∇ and F=f². L preserves radial measure. Since L²H=v_{0i}v_{0j}H_ij+[a×(a×y)]·∇H, integration gives

`M_w(H)=∫F[y·∇H−(a·y)∂aH]`.

The spherical average of the first term is zero by differentiating the harmonic mean-value identity in the radius. The first spherical moment of the harmonic function ∂aH is (4πr/3)∇∂aH(c). Thus the other term is **−(4π/3)I_f ∂aaH(c)** for every harmonic polynomial, including translated and nonhomogeneous ones. This verifies the full identity, not a finite multipole truncation. Applying it to the exterior kernel gives −(4π/3)I_f ∂aaG and exactly the author's formula (3.2).

A useful independent check on (3.3) is integration by parts, with the original smooth compact F:

`Q_0(r)=−(2/3)∫_r^∞ sF(s)ds`,

`Q_2(r)=−(2/3)r^(−3)∫_0^r s⁴F(s)ds`.

Substitution into the radial −Δ equations gives precisely S_0=−2F−(2/3)rF′ and S_2=(2/3)rF′. Below the inner shell Q_0 is constant and Q_2=0. Beyond the outer shell Q_0=0 and Q_2=−2I_f/(3r³). These are algebraic consequences of the original formula; no pressure repair has been introduced. They also verify its safe evaluation at the center.

For Lemma 3.3 the supports of the three radial profiles are disjoint **at the same center**. Hence V⊗V is the sum of the individual quadratic tensors. Equal I_f and an orthonormal axis triple cancel the entire exterior expression because Σ(a_j·ω)²=1. The sum of smooth Newtonian pressures is already smooth everywhere and vanishes outside the largest radius. Individual pressures can overlap inside that ball; pressure appears linearly, so this causes no nonlinear cross term. The auxiliary normalizers have computable strictly positive denominators using a rational subinterval of a fixed bump's positive region. Their square roots and derivatives are effective fixed constants.

On the active plateau V=a×y exactly. Radius is conserved, and the observed trajectory cannot migrate into an auxiliary shell. The proof never claims stationary Euler balance. Generally (V·∇)V+∇P is a **nonzero** compact solenoidal field. For example, the varying radial coefficient in a single swirl produces a nonzero curl of its acceleration at suitable points in a transition shell. A stationary-Euler localization theorem is neither used nor needed.

## Small-angle gate, loading and all-time observation

Section 5 fixes a=e1 or e2, so e3 is perpendicular to the active axis. Put Jd=a×d, z=64b/h and θ=2 arctan z. On the perpendicular plane J²=−I, and

`(I−R_(−θ))^(−1)=I/2−J/(2z)`.

Thus the specified c2−c1=d/2−hJd/(128b) gives **R_(−θ,c2) R_(θ,c1)(x)=x+d**. This is the ordered positive first rotation followed by the negative second one. The component parallel to a is unchanged. A reversed J sign or different order is not interchangeable. d=0 remains legal: the two small rotations cancel at the endpoint; b is still positive and no division by d is performed.

The starting radius is h/32. The first pulse moves the marked point at most (h/32)θ≤4b at every intermediate time. With |c2−c1|≤b/2+h/128, the second starting radius lies between h/32−h/128−9b/2 and h/32+h/128+9b/2. At b/h≤1/4096 these normalized endpoints are

`183/8192 > 1/64`,  `329/8192 < 1/16`.

The second radius is conserved throughout its pulse. This proves active-plateau residence at **every** intermediate time, including the intervening zero collar. It is not merely an endpoint check. The velocity and pressure support about the address has radius at most

`h(1/8+1/32+1/128+1/8192)=1345h/8192 < h/4`.

This bound includes both centers and both auxiliary shells. It is the support bound used in the global construction.

The pulses 2θθ′(2s) and −2θθ′(2s−1) are supported in [1/8,3/8] and [5/8,7/8]. There are zero collars both at the half-slot join and at each unit-slot endpoint. All derivatives vanish there. Each time derivative of either angular speed is O(b/h). Centers and scale remain constant within each pulse; no differentiation of a moving center is hidden in the estimates.

The loading construction uses a different fixed balanced template with plateau at radius 1/2. The first half-turn has scale y0 and center (0,y0/2,0), keeps x1=0 and ends at (0,y0,0). The input gives y0 rational, so its zero/nonzero decision is legitimate. If positive but tiny, inverse powers of y0 give large **finite effective input-dependent** bounds. The second half-turn has scale one and center (−1/2,y0,0); throughout it x1=−1/2+(1/2)cosφ lies in [−1,0]. Both paths remain on their primary plateau, and the pulses do not overlap. Loading never enters the open detector x1<−1, including an initially terminal machine.

In each nonterminal computational slot, a=e1, d=(0,v,0), and both rotation centers have x1=−1. The tracked point therefore has x1=−1 during **both pulses and both collars**. An auxiliary swirl may change x1 elsewhere, but does not act on this point. At a terminal code the second pulse ends at x1=−1−b_n, strictly inside the detector. This includes initial halting in the first computational slot. The formula continues to define the fields for all later times; a symbolic post-halt trajectory is unnecessary for the event equivalence.

## Global field, budgets and uniqueness

C80 keeps RV's exact h=δ_n and b=b_n. The accepted bounds give b/h≤δ_n^(n+9)≤2^(−144)<1/4096, with no new scale or clock selection. The finite index set m=0,…,D_n includes every actual address. The source divisibility identity reads the newest k_n from m mod M_n despite the retained earlier records. The nonterminal endpoint becomes y_(n+1); the terminal endpoint moves into the detector. Induction is used only to prove this trajectory statement.

At each time, distinct addresses are h apart and each entire **velocity and pressure** support is contained in its h/4 address ball. Only one pulse at each address is active. Hence all cross-address velocity products vanish, and S_(Σu_m)=ΣS_(u_m). The sum of the local compact pressures solves the global pressure equation and is its decaying representative. No overlapping pressure tails are omitted. There is no convolution cutoff or subsequent Leray projection that could reintroduce a tail. The enormous but finite number of addresses does not multiply spatial supremum bounds, including derivative bounds at support boundaries.

Differentiating u=ωhV((x−c)/h) and p=ω²h²P((x−c)/h) gives, for every fixed l and α,

`||∂t^l∂x^α u||∞ ≤ C b h^(−|α|)`,

`||∂t^l∂x^α p||∞ ≤ C b² h^(−|α|)`.

For ω² the Leibniz rule has finitely many terms, each the product of two O(b/h) factors, even at arbitrary fixed time order. The dimensionless centers depend on the bounded parameter d/b; they introduce no additional inverse b factor. The residual's time derivative and Laplacian terms are bounded by C b h^(−|α|−2) when h≤1. Every nonlinear derivative and every pressure-gradient derivative is bounded by C b²h^(−|α|−1). This verifies (5.3) for all fixed mixed orders, including viscosity dependence. A half-turn at reading scale h or a fixed angle at writing scale b would not satisfy these bounds; the author's small-angle construction does.

On slot n the two worst powers become δ_n^(n+8−|α|) and δ_n^(2n+19−|α|). For n≥max(|α|,J,4), s_n≥n² and 1+t+|x|≤n+7≤2^n give the bound C2^(Jn−n²)≤C. All earlier slots and loading are a finite effective maximum. This proves each derivative-order/weight claim separately; it asserts no order-uniform constant. The same estimates for u imply ∫0∞||u(t)||∞dt<∞, hence finite length for every material path.

Loading centers have norm below √5/2 and loading support radius at most 0.8. Later addresses have norm at most √2, with support radius below 1/4. Thus the **same input-independent** closed ball B4 contains u,p,f for every time. Derivatives and the residual do not enlarge support. Smooth zero collars ensure local smoothness across all time joins; there are only finitely many slots on every bounded time interval and no finite accumulation time. The initial velocity is zero.

The constructed pair has U∈C_tH2∩C_t^1L2 and P∈C_tH1 on every finite interval, not merely slice membership: common compact support and the continuous bounded derivatives give these norm continuities by dominated convergence. U and ∇U are bounded there. This checks every reference hypothesis of RV's nonzero-pressure comparison lemma. Its difference-energy inequality uses the reference ∇U and cancels q=p−P using exactly the stipulated pressure class. It proves velocity uniqueness; the H1 representative fixes the possible spatial pressure constant on R3. The expressly permitted competitor-gradient relaxation is valid. No unrestricted weak-solution uniqueness, arbitrary-pressure uniqueness for C80, or general Navier–Stokes regularity is inferred.

## Effective evaluation and moduli

The original finite prescription is an all-address compiler. It computes the finite table, k0, capacities and scales, and at time slot n installs F_n and h_n on **every** residue class. An evaluation performs a finite enumeration of m=0,…,D_n and one transition lookup per summand. It never obtains the infinite executed sequence k_n in order to prescribe f. No efficiency or polynomial-time claim is made.

An enclosure of a computable time supplies a finite superset of possibly relevant slots; it is also permissible to use all slots below a rational upper bound for that time. The fixed flat collars and effective RV cutoff bounds make these expressions computable at undecidable time joins. This requires no floor operation or equality test on the supplied real time. Rational arithmetic handles d/b and all centers, while arctan and the fixed positive square roots are effective with usual error bounds.

For radial pressure evaluation, use the inner polynomial formula when r<1/512 and the original quotient formula when r>1/1024 in normalized small-gate coordinates. These two open tests cover every radius and agree on their overlap, so interval refinement certifies at least one. There is no test “r=0.” The loading template has its own fixed positive inner collar, scaled by its known positive rational scale. Ordinary differentiation of these coincident smooth formulas evaluates every requested derivative.

The claimed effective bounds provide an actual modulus, not just a finite collection of sample checks. For any one requested derivative g=∂t^l∂x^α of u,p or f, compute the J=0 bounds at (l+1,α) and (l,α+e_i), i=1,2,3. A rational upper bound L on their sum gives

`|g(t,x)−g(s,y)| ≤ L(|t−s|+Σ_i|x_i−y_i|)`.

Approximate the arguments within ε/[8(1+L)] in this sum norm. Effective fixed-profile derivative bounds likewise bound one-dimensional quadrature errors: for an integrand with derivative bound K on an interval of length A, a mesh with width at most ε/[8(1+AK)] gives a sufficient Riemann-sum error bound. Finite differentiation and product/quotient rules propagate these bounds through the pressure formula on the positive-radius chart; the center chart is polynomial. These are direct procedures from the original fixed templates and bounds, not new mathematical hypotheses.

Growing grid counts affect **numerical error allocation**, although they do not affect sup norms. For N summands in a finite time/address superset, allocate an error budget ε/(8N) per summand (and divide further among its finite arithmetic/integration operations). N is a known finite integer, however large. Thus a finite sum can meet the requested total error even with undecidable support membership. No oracle for the active address or the trace is needed. This also supplies all derivative-order and weighted constants required in C80.

Viscosity enters precisely as −νΔu in f. The other coefficients are effective independently of ν. For computable ν>0, the numerical compiler and bounds are computable; for an arbitrary fixed positive noncomputable ν they are relative to that parameter, as stated. This does not claim unconditional computability at a noncomputable viscosity.

## Separate audit of the unused finite-completion route

For Lemma 4.1 use normalized spherical measure consistently. With an orthonormal harmonic basis, b(ω)=B+ΣM_v(H_lm)Y_lm/[l(l−1)ρ^(l−2)] is strictly positive because B is a strict computable upper bound on the absolute value of the other terms. The N+1 Gauss–Legendre nodes and 2N+1 equally spaced azimuths integrate every restricted polynomial of degree ≤2N exactly: nonzero azimuthal frequencies have magnitude at most 2N and are annihilated; the zero mode is a polynomial in z of degree ≤2N. The supplied orthogonality argument gives simple interior nodes and positive weights. Finitely many separated nodes have an effective positive separation, so sufficiently small disjoint swirl balls fit within the prescribed shell. Their amplitudes are computable positive square roots for effectively supplied geometric/data parameters; no uniform cost as N→∞ is asserted.

Euler homogeneity gives ∂ωωH_lm(ρω)=l(l−1)ρ^(l−2)Y_lm(ω). Lemma 3.2 and cubature therefore make the added moment exactly −M_v(H_lm): the constant B is orthogonal to all degrees ≥2, and bY_lm has degree at most 2N. The swirl balls are disjoint from the core and from one another, so no quadratic cross term is overlooked. Degrees zero and one vanish automatically. This proves the **finite** claim while preserving v on the core.

For the counterexample, H4=Σx_i⁴−(3/5)|x|⁴ is harmonic. At each c=±Re_i, ∂iiH4(c)=24R²/5, giving six-swirl moment **−(144/5)c_f R²≠0**. Equal disjoint swirls have total isotropic energy tensor. Nevertheless their fourth harmonic moment is nonzero, so their pressure is not compact. This is an actual smooth velocity counterexample to the proposed quadratic shortcut, not an abstract stress-only example. Disjoint balls are available by taking their radii small relative to R>0.

The infinite shell proposal has the precise unpaid obligations acknowledged in I80: common smooth tail control, quantitative packing/separation, temporal coefficient derivatives and square-root margins, and a computable modulus at the limiting sphere. Finite completion does not supply them. That gap cannot refute C80: its balanced gate cancels **all degrees with three components at one center**, and never invokes infinite completion.

## Independent diagnostics, domain and primary-source limits

[diagnostics.py](../experiments/i85_compact_solenoidal_computation_r2/diagnostics.py) was independently written. It constructs harmonic bases by polynomial Cauchy data (rather than copying the author's Laplacian-kernel diagnostic), retains independent radial moments, and checks translated tensors. Its exact output records 162 cases over complete harmonic bases in degrees 0–8, two radial Poisson identities, a symbolic all-angle ordered-rotation identity and wrong-sign obstruction, the exact plateau/support fractions, the −144/5 fourth moment, a nonzero cross term if radial disjointness is dropped, a rank-32 finite harmonic Gram matrix, a finite-grid error budget, and 3,030 decay-exponent checks. These are finite diagnostics and algebraic stress tests, not proofs of all-degree cancellation, all-time computation, infinite-order smoothness, or universality. Those conclusions rest on the analytic arguments above and the stipulated interfaces.

The complete tree has 13,223 entries, 749 manuscripts and 10,373 blobs. I85 uses I79's complete domain by immutable reference, with the 9,340 I14 text bodies, all 1,033 outside original blobs, **776 actual PDF extractions** and 257 other outside byte bodies. The two independent full-domain searches preserve exact hit multisets, including duplicate paths/versions: pressure-locality has 129 hits and fluid-mechanisms 610. The remaining non-PDF bytes are decoded with UTF-8 replacement for that search; this is not image OCR or semantic reading. The verifier checks every original Git blob identity, every searched-body hash, the exact domain partition, and re-extracts all 776 PDFs to stdout. It does not duplicate the roughly 619 MB outside archive. [Compiled passages](../sources/i85_compact_solenoidal_computation_r2/compiled-passages.json) separately bind actual reading of RV's pressure/compiler contracts, GS direct forcing and FP comparison in the compiled PDF bodies.

Primary comparison is deliberately bounded to the retained 2026-10-10 response/version records and actual body passages in [primary-passages.json](../sources/i85_compact_solenoidal_computation_r2/primary-passages.json). Cardona–Miranda–Peralta-Salas v3 Theorem 1 uses a noncompact Euclidean computation set and infinite energy; Theorem 26 and Remark 29 concern bounded-tape torus simulations and nonzero Beltrami initial velocity. DGMP arXiv v1 Theorem A and the UPC April 15, 2026 manuscript explicitly deform the metric and use the Hodge-harmonic setting. The file historically named `dgmp-published` is a watermarked draft, not a verified publisher final. Gavrilov and Constantin–La–Vicol supply stationary-Euler localization precedents with extra first-integral/localizability constraints. Brandolese–Meyer Remark 2.6/Corollary 2.7 supply higher moment obstructions; Theorem 3.1 is conditional spatial-decay persistence. Brandolese–Okabe v1 Theorem 2.1 treats a matrix divergence-form control, small data and a specific little-oh energy rate. None of these statements is silently imported as a premise or dismissed on abstract-only evidence. Their entire proofs have not been independently audited here, and this bounded comparison certifies neither worldwide priority nor substantial contribution.

The original author and parent evidence-only responses are retained alongside this review. [preseal-events.json](../sources/i85_compact_solenoidal_computation_r2/preseal-events.json) records missing-runtime attempts, truncated reading deliveries and completed rereads, failed filename guesses, and verifier corrections. Corrections to diagnostic/verifier machinery are distinct from mathematical changes: **the author proof was not repaired**.

## Offline reproduction and remaining decisions

Run from the project directory:

```sh
python3 -B frontier/experiments/i85_compact_solenoidal_computation_r2/verify.py
```

The verifier is offline and read-only. The seal covers the complete owned report/source/experiment domain, including the exact pure-Python diagnostic wheels, frozen snapshots, failures and earlier replay outputs. Only its own seal file is omitted from the seal inventory. It verifies immutable references and original author evidence, the full 10,373-blob domain, all outside PDF extraction bytes, search multisets, source/version/passages/coverage, retained primary responses and exact independent diagnostic output. Only the four named live ledgers may drift informationally; no other reference is excused. It does not fetch, rewrite seals, repair data, create caches, stage or commit.

Evidence status is reported separately as **PASS_EVIDENCE_ONLY** after replay. The mathematical verdict is **ORIGINAL PASS WITHOUT REPAIRS** for C80 and its used arguments. The finite-completion lemma also passes in its finite scope, and the fourth-moment counterexample is confirmed, both unused by C80. Unbounded arbitrary-core completion remains open; G and R remain outside this review's nominated scope. The parent still controls contribution review, acceptance, count and publication.
