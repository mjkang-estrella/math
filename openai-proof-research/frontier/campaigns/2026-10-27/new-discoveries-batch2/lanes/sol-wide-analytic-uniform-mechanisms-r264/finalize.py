from pathlib import Path
import json,hashlib,datetime,xml.etree.ElementTree as E
from fractions import Fraction as F
L=Path(__file__).resolve().parent
def write(n,t): (L/n).write_text(t.strip()+'\n')
write('SCOUTING.md',r'''
# Twelve primary-body question screens — r264

30 October 2026 UTC. **Zero qualified survivors and zero discovery credit requested.** The two first entries are research leads with unresolved mathematical and eligibility gates, not results awaiting only formalization. No separate count for clauses, tools, endpoints or special cases. Root alone accepts/counts; 9 additional /39 total /next40 unchanged.

Every versioned identifier below links to the downloaded primary PDF; access.jsonl records exact URL, timestamp, headers and SHA256. Sources were copied/hash-bound before extraction and reading. This is a bounded proof-body screen, not a comprehensive audit of each paper or a claim to have read every cited predecessor. The 876-report immutable history index was verified in place; r259/r261 and r260/r262 scouting reports were frozen before reading. Exact-ID and author/semantic alias screens are retained. Generic surname hits are not asserted duplicates. The propeller family was caught as historical and removed from the twelve, without re-solving it. Banić–Elezović and all explicit excluded families were not pursued.

|#|Attributed source question, exact scope|Actual nearest body and disposition|
|---|---|---|
|1|Pavlenkov, [2610.29551v1](https://arxiv.org/pdf/2610.29551v1), §4.4, unnumbered subsequential separation conjecture. One fixed nondegenerate integrable real mark X, iid nonnegative unbounded weights Y independent of marks; T_n=ΣX_iY_i/ΣY_i and d_n=EΣ(Y_i/ΣY_i)^2. For ANY two deterministic subsequences with T converging to Z_1,Z_2 and d converging to d_1,d_2, must d_1≠d_2 imply different laws of Z_1,Z_2?|**INCOMPLETE research lead, not a qualified survivor.** Lemma3.1/AppendixA supplies the dust-plus-ranked-mass representation. Proposition4.6 proves finite variance by uniform integrability; Example4.7 handles a stable mark plus independent nonzero Gaussian noise by two asymptotic exponents. Lenzi2608.24616v3 actual Thms2.1/2.2,6.3 and Remarks9.2/10.5 concern power-sum/full-sequence steps and do not assert this endpoint. Two sustained mechanisms and an exact relaxed collision are in discovery.md. Next: obtain a realizability theorem or a Lévy-transform injectivity statement that uses the common iid weight law. No such bridge proved. No exact historical alias found; current registry clearance unavailable.|
|2|Gontier–Van Den Bosch, [2610.36240v1](https://arxiv.org/pdf/2610.36240v1), Conj1.3: for EVERY p>3, α*(p,3)<∞, i.e. some real V∈L^p(R³) creates a zero mode of −iα·∇+(m−V)β, m>0.|**DEFER, not a nomination.** Actual Prop1.4/§5.3 polar-decomposition proof excludes every radial L^p potential. Thm1.1 gives optimizers at fixed finite budget, not finiteness of the critical budget. A closed radial domain wall has a tangential spectral gap; taking larger walls only approaches zero. A nonradial inverse-spinor construction must solve a scalar real mass compatibility condition, rather than independently prescribing matrix entries. Source explicitly mentions an earlier ununderstood Astra construction, creating an additional provenance/subsumption gate. Next: a decaying spinor whose derivative is pointwise a REAL scalar multiple of βψ with V∈all p>3. No such spinor obtained; no sustained claim here. Current author query found only the source, not a clearance certificate.|
|3|Bucur–Laugesen, [2610.29840v1](https://arxiv.org/pdf/2610.29840v1), Conj3: every n≥3, nonempty bounded open Ω⊂R^n and 1≤p,q≤∞ satisfying 1/q<1/p+2/n has Γ_p,q(Ω)≥Γ_p,q(Ω*) for the clamped quotient ||Δu||_q/||u||_p, infimum over C_c^∞(Ω), Ω* equal-volume ball.|**REJECT major-problem route.** Thm2/§4 gives p=∞,q>n/2 via paired comparison; Thm1/§3 covers dimension2. Actual Lemma8 equality argument retains continuity/capacity conditions. General scope contains unresolved higher-dimensional Rayleigh; interpolation of sharp endpoint constants does not give the conjectured sharp constant. No new mechanism, so no prolonged attack.|
|4|Frank–Hansson question as answered by Levitin–Polterovich–Speciel, [2610.40223v1](https://arxiv.org/pdf/2610.40223v1), Cor3: for bounded nonempty open planar Ω, finite punctures P and real smooth curl-free A on Ω\P, Tr(Λ−H_A)_+^γ≤|Ω|Λ^(γ+1)/(4π(γ+1)) for all Λ≥0, γ≥1, Dirichlet realization.|**PUBLIC EXCLUSION.** Actual Thm1 proof uses the commutator/trace machinery; Cor2 proof completes the square to bound eigenvalue sums and Cor3 integrates the Riesz mean. The source includes every real Aharonov–Bohm flux. Neither γ<1 nor generic nonzero field is silently included. Original2008 body not separately read.|
|5|Xu–Yu, [2610.39490v1](https://arxiv.org/pdf/2610.39490v1), Thm1.1 question: do ALL planar discontinuous piecewise linear systems with two zones separated by one straight line have at most three isolated crossing limit cycles?|**PUBLIC EXCLUSION.** Actual half-return-map derivative proof §2 and §4.4 sign comparison (4.17)–(4.19), followed by equal-parameter scaling §4.5, supply the uniform bound. Sliding or nonisolated periodic orbits are not the question. No new finite-cycle example is credited.|
|6|Bellavita–Dellepiane–Luo, [2610.36943v1](https://arxiv.org/pdf/2610.36943v1), Question1.1 (prior Question6.3): for any b in the Schur class with inner–outer factorization b=b_i b_o and positive finite Borel μ on T, does equality H(b)=D(μ), with equivalent norms, imply H(b_o)=D(μ)?|**PUBLIC EXCLUSION.** Actual Thm1.2/§3 proves nonextremality and the Corona pair property, hence outer-factor equality. Lemma3.1 uses a glued subharmonic function and Poisson domination, not boundary pointwise bounds alone. Thm1.3's countable-Corona/potential bridge gives the full accompanying characterization. Original posing body not independently obtained.|
|7|Damanik–Li–Strungaru, [2610.36403v1](https://arxiv.org/pdf/2610.36403v1), modified Deift/Kotani–Last family: Weyl/generalized almost periodicity under the exact Sodin–Yuditskii hypotheses. Thm1.1 assumes E satisfies FGLC,KGLC(k=0,1),RPWS,WH and nonexceptional q∈R(E); Thm1.2 assumes FGLC,RPWS, q∈R(E) and purely absolutely continuous Schrödinger spectrum.|**PUBLIC RESTRICTED-SCOPE EXCLUSION; no unrestricted theorem.** Actual §4 flow argument transfers generalized almost periodicity from compact-group/Riemann-integrable sampling. Original Bohr versions are reported disproved, but their predecessor counterexample bodies were not separately audited. WH and nonexceptionality cannot be removed from Thm1.1 on this evidence. No broad original-conjecture resolution claimed.|
|8|Medvedev's hyperbolic critical-catenoid index question, Dorofeev–Pigazzini, [2610.35651v1](https://arxiv.org/pdf/2610.35651v1), Thm1: EVERY a>1/2 in the angular-period-2π critical spherical catenoid family in H³ has index4 and nullity2.|**PUBLIC EXCLUSION.** Actual §6 Riccati proof separates a≤1 from a>1 by the sign change of (6v²+4−4a²)/(v²+2+D(v)); Wronskian boundary comparison and the ground-state identity handle higher modes. This is global parameter scope, not merely the older near-endpoint result. Original Medvedev body unread.|
|9|Choe et al. compactness-parameter question, Liu–Ma, [2610.33717v1](https://arxiv.org/pdf/2610.33717v1), Thm3.8: any finite nonzero-coefficient linear combination Σa_i C_φi of bounded composition operators on Hardy T_p of a (q+1)-homogeneous rooted tree, q≥2, has compactness independent of 1≤p<∞.|**PUBLIC TREE-SCOPE EXCLUSION; disk question not claimed solved.** Actual Thm3.8 proof bounds nonzero subset sums of the finitely many coefficients above and away from zero, comparing N_Q,p tails via Thm3.3. Source Conj3.7 literally concerns classical disk H^p, p>0; replacing that domain by a tree is a scope restriction, not a proof of the literal disk conjecture. No new endpoint extrapolation.|
|10|Dinh's corrected BMV pinching question, Dinh–Le–Vuong, [2610.31851v1](https://arxiv.org/pdf/2610.31851v1), Thm4.2: for ALL PSD A,B of any finite size and integers n,m≥0, normalized symmetrized word trace A_n,m(A,B)≥A_n,m(A,E_A(B)).|**PUBLIC EXCLUSION.** Actual Thm3.1 proof constructs a positive planar measure by removing selected-root atomic pinching mass; Thm4.2 integrates a^n b^(m−2) with coefficient m(m−1), with m=0,1 equality and commuting equality criterion for m≥2. The earlier clustered-word upper bound is a different, already-refuted assertion. Generic pinching history hits do not make this a new discovery.|
|11|Gonçalves2019 Conj2 as settled by Suzuki, [2610.31543v1](https://arxiv.org/pdf/2610.31543v1), Thm1.2: for EVERY coordinatewise-even f∈L²(R⁴), U(x,t)=(e^{itΔ}f)(x1,x2,x1,x2), ||U||²≤( ||f||²−β dist(f,L²_rad)^2 )/4 with a universal β>0.|**PUBLIC EXCLUSION.** Actual spherical-harmonic/projection proof §§4–5, including the (4.4)–(4.6) spectral estimates and final finite-dimensional norm evaluation, gives optimal β=(17−√97)/32. Coordinatewise evenness is retained. Conj1/three-dimensional and tensor consequences are not separate breadth items. Original2019 body unread.|
|12|Li–Zhao, [2610.30700v1](https://arxiv.org/pdf/2610.30700v1), Cor5.1 answering prior Conj1: EVERY positive r,s,m with r≠s mod m and gcd(r,s,m)=1 has commuting N-truncation and n-partition-size limits C_n,N, both I_1/2(r/m,s/m).|**PUBLIC EXCLUSION.** Actual Thm1.1/§5 proof combines Boltzmann conditioning/Fourier convergence with log-Gamma limit; Cor5.1 compares the independently computed finite-truncation Beta limit. The gcd condition is used by the finite-set theorem, so it is retained even though the unrestricted calculation does not need it. No fresh limit interchange claimed.|

No ranking of purported real survivors is manufactured. The only sustained fresh full-scope attempt was item1. Current arXiv metadata/searches are bounded and date-stamped; current public proof-registry heads were not obtained. All inherited denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes remain parked, without retries or bypasses. No worldwide priority assertion.
''')
write('discovery.md',r'''
# Sustained attempt: subsequential separation, not a source resolution

Target: Pavlenkov2610.29551v1 §4.4 as quantified in SCOUTING item1. The same iid law of Y must generate BOTH subsequences. Normalize on S_n>0; its complement has probability tending to zero. Center X, writing EX=0. Lemma3.1 gives limits Z(P)=ΣP_jX_j (dust contributes EX=0) and d(P)=EΣP_j². The source already proves finite variance, endpoint d=0, endpoint d=1, and stable-plus-Gaussian marks; none is a discovery here.

## Mechanism A: truncation and convex test functions

For symmetric integrable X set X_M=sign(X)min(|X|,M), also centered. Conditional contraction gives E|Z(P;X)−Z(P;X_M)|≤δ_M=E(|X|−M)_+, uniformly in EVERY random subprobability partition. For bounded X_M the exact identity is E Z(P;X_M)²=σ_M² d(P). If the original two marked limits agree in law, truncation only gives Wasserstein distance at most 2δ_M between the truncated marked limits. Since these are supported on [−M,M], the square function is 2M-Lipschitz there. Thus

    σ_M² |d(P)−d(Q)| ≤ 4Mδ_M.

This is a valid bound but does NOT force the desired equality for arbitrary integrable X. For symmetric Pareto |X| with P(|X|>t)=t^(−3/2) for t≥1,

    δ_M=2/sqrt(M),   σ_M²=4sqrt(M)−3,
    4Mδ_M/σ_M²=8sqrt(M)/(4sqrt(M)−3) → 2.

Exact rational checks at square cutoffs are retained. An attempt to use convex truncated quadratic functions encounters the same tail-scale contribution; no unproved exchange of the M→∞ and subsequence limits is used. This is an obstruction to this PARTICULAR quantitative truncation route, not proof of falsity of the conjecture or of all truncation arguments.

The source's absolute-value Jensen gap gives a strict loss from the original X when d<1; it is one-sided and does not order two arbitrary internal d values. Strict convexity likewise compares partitions under an actual refinement coupling. No such ordering follows merely from d(P)<d(Q).

## Mechanism B: stable characteristic products, then iid realizability

Take a symmetric α-stable integrable mark, φ_X(t)=exp(−|t|^α), with α=log(2)/log(3/2). Because 3/2<2<(3/2)², 1<α<2. Consider deterministic subprobability partitions

    P=(3/4,0,0,…), with dust1/4;
    Q=(1/2,1/2,0,…), with dust0.

Their marked characteristic functions are identical for ALL real t, since (3/4)^α=2(1/2)^α, while

    d(P)=9/16, d(Q)=1/2, d(P)−d(Q)=1/16.

Thus the tempting arbitrary-mass-partition strengthening of the source is rigorously false, even with a nondegenerate integrable mark. This is a classical stable-law mechanism, receives NO separate credit and is NOT a refutation of the source. The missing hypothesis is precisely realizability as two limits from ONE iid nonnegative weight law. It cannot be supplied by conditioning on a desired number of large weights.

To move beyond that shortcut, consider the standard rare-level iid construction: if a level occurs with probability q_k→0 and n_k q_k→c>0 while higher levels disappear, the count at that level converges to Poisson(c). A fixed deterministic number of large atoms does not result: P(N=j)=e^(−c)c^j/j!, with every nonnegative j retaining positive mass. With negligible lower-level sum and at least one large atom, the conditional partition has N equal atoms. Its stable scale is K=N^(1−α), and d=1/N. K is strictly decreasing in N≥1, so equality of its FULL distribution determines that of N and therefore d. A collision in a finite sweep of expected K would not suffice. Empty-level and nonnegligible dust cases also must be retained, not conditioned away.

With lower-level drift b and large-jump size a the compound-Poisson model instead has

    K=N/(b/a+N)^α,    d=N/(b/a+N)²,
    K'(x)=(b/a−(α−1)x)/(b/a+x)^(α+1).

This nonmonotonicity leaves an inverse-law problem; matching one moment does not match the entire K distribution. No pair of full normalized-jump laws with identical K law and different expected d, and no common-iid embedding, has been established. These formulas identify a concrete next calculation, beyond a finite sweep or one failed shortcut.

## Closest actual prior proof and a third bridge check

Lenzi2608.24616v3 predates the source: version3 dated10 September2026 versus Pavlenkov21 October2026. Actual Thm6.3 proof uses the full-sequence inverse theorem5.1 and depoissonization; Remarks9.2/10.5 explicitly prohibit replacing endpoint limits with subsequences in the relevant elasticity/Tauberian steps. Thms2.1/2.2 are stronger local tools than finite variance but do NOT automatically identify quadratic concentration for every mark: for moment abscissa α∈(1,2), the universally supplied limiting power sum is at α. The exact stable collision above explains that distinction.

Conditional on a fractional power-sum bound EΣP_j^r≤C, r<1, Lenzi Thm2.1 says that marks with moment abscissa1 force convergence of each expected power sum for 1<p<2. Interleaving the two candidate sequences then gives equality of those power sums; bounded holomorphic power-sum transforms on Re(s)>1 and the identity theorem would give equality at2. This is a source-dependent subclass bridge, not a new standalone result. The required r<1 bound is absent from the arbitrary-subsequence hypothesis; no blanket application is justified. For stable marks the abscissa lies strictly between1 and2 and the bridge does not apply.

Gao–Konstantinides–Passalidis–Wang–Xu2602.23112v4 was checked after the current Breiman search. Its actual Lemma2.2/proof machinery extends product-tail Breiman asymptotics in risk models, not the normalized-weight subsequential separation assertion. This is a title/alias exclusion, not an asserted subsumer.

Status: INCOMPLETE; no ordinary proof/refutation of the full source result, no PROOF.md, no formalization or manuscript. Decisive next work is the compound-Poisson/normalized-subordinator inverse-law problem with common-iid realizability, or a source-specific theorem obtaining quadratic concentration directly from a marked subsequential law. Novelty and current registry gates remain HOLD.
''')
write('SUMMARY.md','''# r264 handback

Twelve distinct analytic/probabilistic/geometric primary-body question families screened. **Zero qualified survivors; no discovery credit requested.** Public resolutions are excluded with exact scopes; original-body and registry limitations remain explicit.

Strongest fresh attempt: Pavlenkov2610.29551v1 §4.4 subsequential separation principle. Two mechanisms sustained: quantitative truncation/convex tests, and stable characteristic products followed by iid/compound-Poisson realizability. An exact stable-law collision disproves only an arbitrary-partition strengthening; it does not refute the source. Lenzi2608.24616v3's actual proof bodies do not supply the missing arbitrary-subsequence bridge. See discovery.md for equations and decisive next calculation.

876 immutable history references verified in place; r259/r261 and r260/r262 reports read from frozen copies. Propeller was detected as historical and excluded from the twelve. No Banić–Elezović review interference or explicit excluded-family continuation. No shared/git/public/browser/MathDB/Lean/manuscript edits.

All helper/retrieval/hash work used the prescribed guard, fixed AS/groupRSS512MiB CPU210s wall230s, thread environment1 and no cap increases. Final manifest excludes itself and verification-receipt.json; verify.py runs separately after writes. Sources are checked against originals and immutable references; administrative files are snapshot-only. Counts unchanged: **9 additional /39 total /next40**, root alone accepts/counts.
''')
write('progress.md','''# Progress

Administrative ledger and prior campaign context snapshotted; source freeze established before source reading. Recent/broader history checked with immutable references, without recursive evidence duplication. Current arXiv source query retrieved; exact identifiers and semantic aliases screened before sustained work. Twelve families body-screened, historical propeller removed and replaced by Li–Zhao. No eligible full result found. Pavlenkov route sustained through truncation, stable characteristic products and normalized iid realization constraints; mathematical gaps retained. Final artifacts and bounded checks written; separate final-byte/source/reference verification follows. Counts9/39/next40 remain unchanged.
''')
write('FAILURES.md','''# Failures and bounds

1. First native administrative cat returned truncated output from the large ledger/context. Both files were subsequently snapshotted in full and parsed under the guard. No full-read claim rests on that truncated display.
2. Several guarded source-excerpt displays exceeded output budgets. Frozen full extracted texts remain; targeted follow-up reads recovered the decisive scopes/proof passages. No unseen broad catalogue is described as a read proof body.
3. pdftotext emitted font-type mismatch warnings for several arXiv PDFs. Exact PDFs are retained; unambiguous extracted statements suffice for triage, not a typeset-formula acceptance certificate.
4. A literal 'Proof of Theorem1.2' marker was absent in Suzuki and a literal 'Proof of Theorem1.1' marker absent in the almost-periodicity paper. Section/proposition proofs were used, without fabricating marker matches.
5. Truncation/variance route gives a nonvanishing error ratio for integrable Pareto marks. Stable collision is valid only in the relaxed partition model; iid realization is missing. No source conjecture is refuted or proved.
6. Lenzi's full-sequence theorem is not transferred through an invalid subsequential Tauberian step. Conditional subclass bridges remain uncredited.
7. Current public proof-registry heads unavailable under inherited denied-route restrictions. No retries of GitHub API/raw/codeload/diff/patch, ScienceDirect or Google challenge routes; no proxy, browser or TLS workaround. No inaccessible historical interval reopened. All HTTP requests in this lane returned200; that is access success, not novelty clearance.
8. Historical index is a bounded876-report index, not all possible later active-lane content. Recent four named scouts were separately frozen/read. Generic alias matches and missing original posing bodies remain limitations. No worldwide priority or exhaustive citer search claimed.
''')
checks={'scope':'exact rational checks; no simulation or source proof certificate','caps':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False},'stable_collision':{'P':[str(F(3,4))],'Q':[str(F(1,2)),str(F(1,2))],'P_square_sum':str(F(9,16)),'Q_square_sum':str(F(1,2)),'difference':str(F(9,16)-F(1,2)),'alpha_interval_certificate':'3/2 < 2 < (3/2)^2=9/4; alpha=log2/log(3/2) in(1,2); (3/2)^alpha=2 exactly'},'pareto_square_cutoffs':[]}
assert F(3,2)<2<F(3,2)**2
for k in [1,2,4,16,256,4096]:
 M=k*k;delta=F(2,k);var=4*k-3;ratio=4*M*delta/var
 checks['pareto_square_cutoffs'].append({'M':M,'delta':str(delta),'clipped_variance':var,'error_ratio':str(ratio)})
 assert ratio>2
write('boundedchecks.json',json.dumps(checks,indent=2))
ns={'a':'http://www.w3.org/2005/Atom'}
chron=[]
for p in [L/'science/query.xml',L/'science/versions.xml',L/'science/breiman-prior.xml']:
 for e in E.parse(p).getroot().findall('a:entry',ns):
  ident=e.findtext('a:id',namespaces=ns)
  if any(k in ident for k in ['29551','24616','36240','23112']):chron.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
write('chronology.json',json.dumps(chron,indent=2))
admin={}
for p in (L/'admin').glob('*.json'):
 d=json.loads(p.read_text());admin[p.name]={'keys':list(d),'accepted_titles':[r.get('title',r.get('proposed_result','')) for r in d.get('accepted',[])],'status':'snapshot only; no original stability assertion'}
write('administrative-read.json',json.dumps(admin,indent=2))
write('provenance.json',json.dumps({'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'primary_bindings':'bindings.jsonl','initial_bindings':'freeze.json','retrievals':'access.jsonl','immutable_history':'history-verified.json','body_excerpts':'body-excerpts.json','chronology':'chronology.json','derived_text_note':'pdftotext derivatives generated after PDF freeze, retained in science; exact PDF authoritative','read_scope':'target and closest proofs read in targeted passages, not a comprehensive audit of all theorem dependencies','registry':'current heads unavailable, inherited denied routes parked','counts':[9,39,40],'credit_requested':0},indent=2))
# Post-read comparison before final manifest. Administrative originals are intentionally excluded.
bindings=json.loads((L/'freeze.json').read_text())+[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
post=[]
for r in bindings:
 if r.get('administrative'):continue
 for key in ['original','copy']:
  assert hashlib.sha256(Path(r[key]).read_bytes()).hexdigest()==r['sha256'],r
 post.append({'path':r['original'],'sha256':r['sha256'],'original_and_copy_match':True})
write('source-postcheck.json',json.dumps(post,indent=2))
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
write('finalmanifest.json',json.dumps(manifest,indent=2))
print(json.dumps({'manifest_files':len(manifest),'source_bindings_verified':len(post),'checks':'PASS','credit_requested':0}))
