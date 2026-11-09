import pathlib,json,hashlib,re,html,datetime
L=pathlib.Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,s): (L/n).write_text(s.strip()+'\n')
access=json.loads((L/'access.json').read_text());chron=[]
for e in access:
 if '/abs/' not in e['url'] or 'path' not in e:continue
 t=(L/e['path']).read_text();plain=html.unescape(re.sub('<[^>]+>',' ',t));plain=re.sub(r'\s+',' ',plain)
 pos=plain.find('Submission history')
 chron.append(dict(url=e['url'],sha256=e['sha256'],retrieved=e['utc'],submission_history=plain[pos:pos+1700],version_strings=sorted(set(re.findall(r'\d{4}\.\d{4,5}v\d+',plain)))))
write('chronology.json',json.dumps(chron,indent=2))
write('SCOUTING.md',r'''
# r259 — twelve distinct source-question families

Screen date 2026-10-30 UTC. **Qualified ranked survivors: zero. Discovery credit requested: zero.** This is a twelve-family screen including public/duplicate exclusions, not twelve newly open questions. Root alone accepts/counts; 9 additional / 39 total / next 40 unchanged. Primary URLs below identify the bodies actually obtained; access.json binds exact original bytes, headers, time and SHA256, freeze.json binds scientific originals/copies, chronology.json retains live submission histories. These current arXiv sources do not clear the unavailable public proof registries.

Early screening: r257 SUMMARY/SCOUTING and r219/r246 alias indexes frozen before use. early-history.json verifies all 876 original-role references from r257's immutable history-bindings.json, before the main body investment. It caught Vígh's chord question as old r17; the fetched chord PDF is retained but excluded from these twelve. expanded-history.json subsequently caught Luo as old r94/r103/r224; it is a compact duplicate exclusion, never a nomination. No recursively copied historical trees. Absence of a token hit is not absence of a mathematical duplicate.

|#|Attributed source question and exact scope|Actual closest body; mechanism, next decisive step and disposition|
|---|---|---|
|1|Hinrichs–Prochno–Sonnleitner random-information question, quoted and answered by Guédon–Litvak–Tatarko–Vritsiou, [2609.24131](https://arxiv.org/pdf/2609.24131), Thm1.10: nonincreasing nonnegative axes σ, p∈(1,∞], p′ conjugate; distinguish usefulness of Gaussian information according to Σσ_j^p′<∞ versus divergence.|**PUBLIC EXCLUSION.** Actual §4.1 proof conditions on the Gaussian left inverse and applies Chevet–Gordon; §6.4 proves the dichotomy. Summable case produces ε_n→0 controlling √n R_n uniformly in ambient N with the high-probability qualification supplied by its proof/Theorem B; divergent case gives f(N)→∞ and P(R_n≥σ_1/2)≥1−2e^(−2n) for n≤f(N). The printed first bullet elides its probability qualifier; no deterministic Gaussian statement inferred. Original 2023 body unread; no fresh resolution claimed. Next step unnecessary for known scope.|
|2|Gómez-Serrano–Levitin–Platt–Polterovich, [2609.10517v1](https://arxiv.org/pdf/2609.10517), Open Problem1.6: does the regular area-π dodecagon maximize κ(K)=dist(0,{ξ: Fourier(1_K)(ξ)=0}) over **every bounded convex centrally symmetric planar domain of area π**?|**INCOMPLETE FRESH ROUTE, not qualified survivor.** Actual Thm1.7/§3.3 locates minimizing directions of regular polygons; Thm1.5/§4.4 compares every regular 2n-gon and disk. Neither treats all domains. §2's anisotropic higher-dimensional construction was checked before solving. discovery.md pursues global anisotropic and local shape mechanisms with exact obstructions/variation identities. Need a convex symmetric perturbation with a certified improvement in the minimum over every direction, or a global upper bound. No current registry clearance.|
|3|González Cázares–Kramer-Bang–Mijatović, [2610.20916v1](https://arxiv.org/pdf/2610.20916), recalled 2024 Conj1.9: every real infinite-variation Lévy process is abrupt or strongly eroded, equivalently J_X(I)=∫_0^1 P(X_t/t∈I)dt/t finite for every bounded interval, or infinite for every positive-length interval.|**PUBLIC EXCLUSION.** Actual Thm1.1 proof p12 separates frequencies |ψ(u)|>Mu from a logarithmically small exceptional set, transferring integrability between intervals. Vigon's stronger point-hitting conjecture is separately refuted by Thm1.2; no splitting that into another breadth entry. Old originals unread; no new candidate.|
|4|Ball–Nayar–Tkocz: for every iid log-concave real pair X,Y, is t↦h(√t X+√(1−t)Y) concave on [0,1]? [Luo2609.11418v2](https://arxiv.org/pdf/2609.11418), Thms1.1/1.2.|**DUPLICATE/PUBLIC EXCLUSION.** Exact endpoint/Hermite convolution proof §3 read. Asymmetric counterexamples exist at every fixed q>0 after Gaussian smoothing; symmetric ones at every q>4/7. The symmetric q≤4/7 classification is old r94 and is not reopened. No extra family for either clause.|
|5|Cheng–Geng Gaussian completely monotone conjecture: every admissible real density f, every integer k≥1 and t>0 has (−1)^k d^k/dt^k ∫P_t f log(P_t f)≥0. [Zou–Fan–Gao–Wang2608.30275](https://arxiv.org/pdf/2608.30275), Eq2/Thm1.|**PUBLIC EXCLUSION.** Actual periodic two-frequency proof §II and closing Thm1 proof read: f_m∝exp(−κ_m x²/2)(1+a_m cos x+b_m cos2x), smooth strictly log-concave; negative signed m-th derivative for sufficiently large m persists for small positive t. Dominant level j3 coefficient −11/96, not a new computed witness. Gu–Sellke predecessor is quoted, not separately body-audited.|
|6|Andrews–Clutterbuck–Hauer Robin Conj1.1 as reproduced by Ye–Zhang [2609.06223](https://arxiv.org/pdf/2609.06223): for every bounded convex Ω⊂R^n, ∃α_0(Ω)>0 such that every α≥α_0 gives a log-concave positive first Robin eigenfunction.|**DEFER GENERAL SCOPE; EXCLUDE KNOWN SMOOTH SCOPE.** Actual Thm1.4 and final joint proof of Thms1.3/1.4 prove bounded uniformly convex C^{3,1} Ω, using C² convergence inside and boundary collar positivity. Losing curvature lower bounds or C^{3,1} estimates is a real gap: nonsmooth approximation does not keep α_0 uniform. Need a boundary-robust threshold estimate. Original posing body not obtained; no viable new mechanism. Torsion is supporting comparison, not a second entry.|
|7|Kabluchko–Marynych–Prochno exponential-profile question for sequences of convex bodies, specialized to Orlicz K_n={ΣM(x_i)≤nρ}, fixed ρ>0. Sadok [2610.16904](https://arxiv.org/pdf/2610.16904), Thm2.1/Cor2.2: n^−1 log V_{floor(αn)} has a concave continuous limiting profile on all α∈[0,1], uniformly in order.|**PUBLIC EXCLUSION OF EXACT ORLICZ SCOPE.** Actual M1–M2: M even convex, M(0)=0, M(s)>0 for s≠0, C¹(R)∩C²(R\{0}); strict convexity not required. Transform factorization Prop3.1 and tilted-density inversion Prop5.3 supply the mechanism, not homogeneity. General original phrase “sufficiently regular sequences” is not an exact usable hypothesis; original [8] body unread. No general resolution or heterogeneity extension claimed.|
|8|Milman's ε-Dvoretzky polynomial-dependence question. Klartag–Moshe [2610.03204](https://arxiv.org/pdf/2610.03204), Thms1.1–1.3: every convex K⊂R^n with 0 interior, 0<ε<1/2, 2≤ℓ≤n, n≥(C/ε)^((ℓ+1)/2)|log ε| admits an ℓ-section between rB_E and (1+ε)rB_E (universal C).|**PUBLIC EXCLUSION.** Actual Thm1.3 proof uses a net and uniform sampling in the convex body of operators T with T(B^ℓ)⊂K, instead of Haar subspaces. Ball rather than ellipsoid endpoint is Thm1.2. An abstract-only claim was not used to infer an improvement. No fresh parameter instance.|
|9|Kalantzopoulos [2610.07248](https://arxiv.org/pdf/2610.07248), Question1: classify all triples of origin-symmetric convex K, SPD Σ and symmetric A for which Var_{μ_K,Σ}⟨AΣ^−1 y,y⟩≤E⟨(A²Σ^−1+AΣ^−1 A)y,y⟩.|**REJECT FAMOUS-HARD DISGUISE at general scope.** Actual Prop3 identifies coordinate boxes with diagonal A as equivalent to log-Brunn–Minkowski. Actual Thms1–2 prove commuting and eigenbasis-unconditional cases; proof uses even Gaussian Poincaré and decomposition of quadratic forms. Arbitrarily rotated counterexample boxes do not refute the coordinate-box conjecture. No new mechanism beyond the equivalent major problem, so no significant solving.|
|10|Nirenberg1962 universal exclusion of closed asymptotic curves in a negative-curvature annulus bounded by convex curves in tangent planes, as explicitly posed by Banks–Ghomi–Qiu–Raffaelli [2610.13848](https://arxiv.org/pdf/2610.13848).|**PUBLIC EXCLUSION.** Actual Thm1.1/§4 proof supplies smooth embedded annulus with negative curvature in the interior, strictly convex boundary curves in parallel tangent planes, and two closed asymptotic curves. Lelieuvre formula gives first curve; Eq16 Riccati and Lemma4.1 linearization give second. Original1962 body unread; successor theorem directly excludes the quoted scope.|
|11|Domingo-Enrich–Pooladian additive WFR convergence-rate question, attributed by Crucinio–Pathiraja [2609.18118](https://arxiv.org/pdf/2609.18118), §§2,4: can combined Wasserstein/Fisher–Rao rates be added beyond warm-start regimes?|**PARK ORIGINAL-SCOPE GAP.** Actual Prop1 proof gives J(μ_t,π)≤J(μ_0,π)e^{−(α_π+1)t} under its Theorem1 and Assumptions1–2 (strong convexity/smoothness of V_π,V_0, V_0−(1+δ)V_π/2 strongly convex, and −ΔV_π/2+|∇V_π|²/4+V_π strongly convex, plus threshold restrictions). Dissipation sums pointwise; bounds along different component trajectories cannot simply be compared. Original conjecture body not obtained and “sum of rates” alone is not exact quantifiers. No manufactured universal refutation. Need original statement before additional solving.|
|12|Barker–Larman single-radius determination, Fish–Ryabogin–Sun–Yaskin [2610.10229](https://arxiv.org/pdf/2610.10229), Problem1.1: for every n≥2, convex bodies K,L with tB²_n⊂int K∩int L for a fixed t>0, does equality of (n−1)-volumes of K∩H,L∩H for **all** H tangent to tB²_n imply K=L? (Here B²_n denotes the Euclidean unit ball.)|**DEFER SINGLE-RADIUS GAP.** Actual Thm6.2 proof uses harmonic-component real analyticity and an infinite set T⊂(−a,a) with an interior accumulation point, then two-center tomography Thm6.1. One t is not an analytic uniqueness set. No finite sample or harmonic truncation settles the question. Original2001 body unread; no new mechanism/qualified survivor.|

Current bounded follow-up searches: exact Fourier-zero and dodecagon terms, and symmetric entropy concavity, archived before reading. They are discovery tools, not completeness certificates. No current public-registry head obtained. Previously denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google-challenge routes were never retried. Old inaccessible historical intervals are parked. No proxy, TLS disabling, browser, external posting, MathDB, git, Lean or manuscript work.
''')
write('discovery.md',r'''
# Sustained full-scope work: planar Fourier-zero maximum

Target is exactly Open Problem1.6 of arXiv2609.10517v1, not the already refuted 2009 ball conjecture and not the already proved regular-polygon comparison. For every bounded convex centrally symmetric planar K of area π, prove κ(K)≤κ(P12), or exhibit one K violating it. No qualified survivor: the following are incomplete research mechanisms, with routine obstructions proved explicitly.

## Mechanism I: global anisotropy, exact failure of the obvious source transfer

The source proves unboundedness in dimensions d≥3 using Ω_{α,d}={|x|+α|y|<1}. Its proof needs positivity without zeros along the long axis. In d2 this is a diamond D_α, a linear image of the square. Write x=u(1/2,1/(2α))+v(1/2,−1/(2α)), |u|,|v|<1. Its Fourier transform is a positive constant times sinc(ξ·c1)sinc(ξ·c2). Its zero set is the union of lines ξ·c_j=kπ, k nonzero integer. Distance to their union is therefore π/max|c_j|=2π/√(1+α^−2). Since area(D_α)=2/α, the area-π rescaling has

    κ² = 8πα/(1+α²) ≤ 4π,

because (α−1)²≥0 for every α>0. This whole anisotropic family is bounded by the square, already strictly worse than P12 by source Thm1.5. This is an exact full-parameter obstruction, not a finite search. Higher-dimensional zero-free-axis reasoning cannot be transplanted to the plane: the triangular planar section profile has real Fourier zeros. No new ordinary source resolution or credit is inferred from this elementary identity.

## Mechanism II: local boundary variation, including an exact affine obstruction

First, any det1 affine path exp(tS), tr S=0, sends the zero set to exp(−tS^T) times the original zero set. If e_j are the twelve side-midpoint minimizing directions from source Thm1.7, the candidate zero κ exp(−tS^T)e_j has radial derivative −κ e_j^T S e_j. The symmetric part suffices, and Σ e_j e_j^T=6I. Thus the derivatives sum to zero and their minimum is ≤0. Since the true nearest zero is no farther than any such tracked zero, the upper right directional derivative of κ along this path is ≤0. **No positive first-order affine improvement is possible.** A pure rotation gives zero; second-order or nonaffine behavior is not settled by this argument.

For genuinely nonaffine changes use the apothem-one dodecagon: a=tan(π/12)=2−√3, A=12a, normals n_j=(cos θ_j,sin θ_j), θ_j=jπ/6. Side points are n_j+s τ_j, −a≤s≤a. Divergence gives the entire profile along e_0:

    F(r)=Σ_j 2a cosθ_j sin(r cosθ_j) sinc(ra sinθ_j)/r.

For an admissible smooth symmetric boundary perturbation with normal velocity v_j(s), the first variations are δA=Σ∫v_j(s)ds and δF=Σ∫v_j(s)cos(r(cosθ_j−s sinθ_j))ds. At a simple tracked root r the implicit-function derivative is −δF/F′(r). Restoring area A by homothety gives

    δr_normalized = −δF/F′(r) + r δA/(2A).

These identities follow by differentiating domain integrals and the scalar implicit equation; they require an actual convex family and a simple root, not arbitrary signed boundary velocities. The bounded calculations use v_j=a^{2k}−s^{2k}, k1..4, whose concavity on a side suggests outward bulges, but a full closed convex-family construction and angular minimum theorem for the perturbed domains were not supplied. They must not be silently assumed.

There is an exact consistency check independent of quadrature: because x·n=1 on every side, divergence of x exp(iξ·x) gives B(r)=2F(r)+rF′(r), where B is the unweighted boundary cosine integral. At a root B=rF′. Uniform side offsets have δA=24a=2A; hence their area-normalized derivative is exactly −r+r=0. This velocity is just polygonal homothety, so no improvement should appear.

boundedchecks.json reports 45-digit mpmath quadrature diagnostics only: tracked root r≈3.78748545616 at apothem1; parabolic-bulge normalized derivative ≈−4.12410835e−5, and the three higher-power bulges are also numerically negative. These are not interval-certified signs, and r is not the source's area-π normalized root. No numerical result establishes full-scope failure or local maximality. The analytic global anisotropy and affine obstructions above go beyond these bounded tests.

The next decisive calculation is a rigorous, convexity-compatible shape-cone sign certificate for the boundary kernel at the root, including control of the minimum over every Fourier direction. A positive tracked direction alone does not suffice. If all feasible first variations are nonpositive, one still needs second-order analysis or a separate global inequality. The source's regular-polygon theorem supplies neither missing bridge. No further solving is justified by merely repeating regular-polygon scans.

## Closest-body and chronology limits

Primary §2 anisotropic proof, §3.3 Jacobi–Anger proof and §4.4 comparison proof were read before the sustained calculations. Source v1 is 9September2026. All exact fetched latest-version histories are in chronology.json; the PDF identifies v1. Bounded current arXiv title/object searches did not provide a full resolution of Open1.6. This does not certify openness or priority. Original BLP2009 full body, a full citing-corpus audit, subscription databases and current public proof-registry heads remain unavailable/unread. No novelty PASS and no PROOF.md.
''')
write('FAILURES.md',r'''
# Preserved limitations and execution failures

1. Initial guarded init failed with FileNotFoundError: R was incorrectly B.parents[2], pointing to frontier/AGENTS.md. Exit1, sampled peak groupRSS33746944 bytes, wall0.12033360300119966s. Corrected to B.parents[3]; no cap change and no scientific reads in the failed helper. The admin copies created before failure remain; the successful init indexed them.
2. The initial native concatenation of ledger/context and broad filename listing produced truncated tool output. Subsequent guarded snapshots and bounded inspections are authoritative. A native pre-freeze head of sources/CONTENTS.md exposed catalogue descriptions (BSD/Milne), a source-freeze ordering failure; no scientific result or candidate here relies on those descriptions. The governing source rule and administrative upstream.json were also read natively. This limitation is not hidden by later hashing.
3. pdftotext emitted twelve “Mismatch between font type and embedded font file” warnings, exit0. Original PDFs retained. Extracted formula typography is not treated as an exact mathematical transcription where ambiguous; random-radius probability qualifier explicitly flagged in SCOUTING.
4. Several broad excerpt displays were truncated; method-excerpts.json retains selected full neighborhoods, and targeted bounded reads supplied the important bodies. The original posing bodies of several historical questions were not obtained. The screen does not claim complete theorem-proof audits for all twelve papers.
5. The closest-body screen caught prior Kuperberg and Luo lanes. Chord source fetched before the old-status hit was acted on; retained, not counted among the twelve. Luo's already resolved question is explicitly a duplicate exclusion, and the old low-signal problem was not solved/reopened.
6. No network errors occurred in these new arXiv requests. This is not registry clearance. All user-denied routes remain parked without any retry. No registry head or complete current proof inventory obtained.
7. mpmath quadrature is not certified interval arithmetic. No source problem solved. Missing convex-family/angular control is substantive. No PROOF.md, Lean or manuscript generated.
''')
write('SUMMARY.md',r'''
# r259 handback

Twelve distinct attributed source-question families screened with actual primary PDFs and nearby proof bodies. **Zero qualified survivors; zero discovery credit requested.** Public resolutions, an old entropy family, famous-hard equivalence and missing original scopes are explicitly excluded/parked. Chord conjecture was caught as old before sustained investment and is outside the twelve.

Strongest fresh full-scope route: arXiv2609.10517v1 Open Problem1.6, planar dodecagon Fourier-zero maximum. Sustained global-anisotropy and local-shape mechanisms give exact diamond-family and first-order affine obstructions, plus explicit boundary variation formulas. Bounded quadrature does not close the convexity/angular-control gap. See discovery.md; no PROOF.md.

Current registry access gaps and original-body gaps remain explicit. early-history.json and expanded-history.json authenticate 876 historical original-role reports without recursively copying them. All scientific source originals/copies are frozen and checked; administrative files are snapshot-only. A pre-freeze catalogue read and the corrected helper-init failure are preserved in FAILURES.md.

Caps fixed: AS/groupRSS512MiB, CPU210s, wall230s; thread env1, no raises. finalmanifest.json excludes itself and verification-receipt.json; verify.py performs a separate guarded final-byte/reference check after writes. Root alone accepts/counts; 9 additional/39 total/next40 unchanged.
''')
write('progress.md',r'''
# Progress

Completed: governing/admin snapshots; r257 and alias review; 876-reference early and expanded history screens; twelve-family primary-body screen; live arXiv metadata/object searches; sustained two-mechanism work; bounded diagnostic calculation; source postcheck and artifact manifest preparation.

Outcome: zero qualified survivors, zero solutions, zero requested credits. Strongest fresh lead remains unresolved, not recommended as acceptance-ready. Final separate verification is recorded only by verification-receipt.json. No shared files, git, browser, public services, MathDB, Lean or manuscript edits. All writes confined to this lane.
''')
prov=dict(lane=str(L),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),screened_families=12,qualified_survivors=[],discovery_credit_requested=0,counts=dict(additional=9,total=39,next=40),resource_caps=dict(address_space_bytes=536870912,process_group_rss_bytes=536870912,cpu_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',registry_current_head=None,registry_status='denied routes parked; no retries',novelty='not cleared; no claims',failures='FAILURES.md',administrative_policy='snapshot only, do not demand unchanged shared files',scientific_policy='freeze before use; original/copy hashes before and after, history reused by authenticated immutable references',selected_guard_receipts=[dict(command='calculations.py',exit=0,peak_group_rss_bytes=16424960,wall_seconds=0.3611633849795908),dict(command='extract',exit=0,peak_group_rss_bytes=42479616,wall_seconds=0.9622196019627154),dict(command='early screen',exit=0,peak_group_rss_bytes=23134208,wall_seconds=0.24057217792142183),dict(command='expanded screen',exit=0,peak_group_rss_bytes=23437312,wall_seconds=0.2805336449528113)])
write('provenance.json',json.dumps(prov,indent=2))
# Postcheck of frozen original/copy bindings; administrative originals are allowed to evolve.
idx=json.loads((L/'freeze.json').read_text())
for e in idx:
 assert digest(L/e['copy'])==e['sha256']
 if e['kind']=='science':assert digest(pathlib.Path(e['original']))==e['sha256']
refs=json.loads((L/'early-history.json').read_text())['verified_references']
for e in refs:assert digest(pathlib.Path(e['path']))==e['sha256']
write('source-postcheck.json',json.dumps(dict(frozen_copies=len(idx),scientific_originals=sum(e['kind']=='science' for e in idx),historical_originals=len(refs),mismatches=[]),indent=2))
excluded={'finalmanifest.json','verification-receipt.json'}
files={str(p.relative_to(L)):dict(sha256=digest(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
write('finalmanifest.json',json.dumps(dict(excludes=sorted(excluded),files=files),indent=2))
print(json.dumps(dict(files=len(files),status='manifest written; separate verification pending')))
