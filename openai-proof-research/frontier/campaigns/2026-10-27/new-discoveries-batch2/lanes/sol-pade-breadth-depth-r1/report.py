from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def put(n,s):(L/n).write_text(s.strip()+'\n')
put('SUMMARY.md',r'''
# Padé depth and finite/algebraic breadth

HOLD / NO SOLUTION / NO COUNT. Counts remain 9 additional, 39 total, next40; root alone accepts. The literal odd-diagonal positivity question is qualified by the original primary body, not invented from a refuted general question. No PROOF.md is issued because no complete source endpoint was proved or refuted.

Original Fasi–Higham author-repository manuscript, Conjecture3.2, printed p8 (PDFp9), says **positive**, for odd denominator degree and arbitrary numerator degree. The preceding paragraph explicitly motivates diagonal optimal degrees. Scardino2610.39051v1, pp1–3 and conclusion, explicitly says k=m remains open after his off-diagonal refutations. Thus the assigned endpoint is an explicitly surviving, practically motivated subcase of one family; it is not the whole original universal conjecture. Both bodies were frozen and checked before/after reading. The original manuscript has not been compared glyph-by-glyph to SIAM's version of record.

Exact integer-scaled recurrence: all 8,020 coefficients for odd m=1,3,...,39 and n=0,...,400 are strictly positive. This is finite evidence only. Four tempting stronger routes have exact obstructions: coefficientwise m→m+2 monotonicity, nonnegative logarithmic coefficients, positive Laplace representation, and reciprocal even-product positivity. The last fails at m11, coefficient w10, by an exact negative fraction; it does NOT refute the original reciprocal.

Sixteen recent primary papers were retrieved and their statements triaged; only three new source families merit continued reserve consideration (symbolic depth, e-positive trees, and dice with a scope ambiguity). Thirteen other bodies are compact exclusions/deferrals; they are not thirteen new unresolved questions. Full proof reading is selective and explicitly identified in SCOUTING. There are only three ranked research leads including the continuing Padé lead; two are difficult reserves, not acceptance-ready nominations. Existing TRIP/SCA/BHR/arborescence and r213–r221 families are not fresh counts.

No current complete proof-registry head was obtained. No priority clearance is claimed. Source/chronology, current arXiv metadata, immutable history bindings, access limitations and hashes are retained. No shared/git/public/browser/MathDB/Lean/manuscript edits or child work. All helper processes use the assigned guard and fixed caps.
''')
put('discovery.md',r'''
# Exact endpoint and research disposition

For each odd integer m≥1 define
q_m(z)=Σ_(j=0)^m (-1)^j binom(m,j)(2m-j)!/(2m)! z^j.
The assigned claim is: for every such m and every integer n≥0, c_(m,n)=[z^n]1/q_m(z)>0. This formal Taylor series exists because q_m(0)=1. Strict positivity, not just nonnegativity, is literal. m1 gives c_n=2^-n. A zero at any allowed pair would refute strict positivity.

Attribution: Fasi–Higham, An Arbitrary Precision Scaling and Squaring Algorithm for the Matrix Exponential, SIAM J.Matrix Anal.Appl.40(2019),1233–1256, doi10.1137/18M1228876, Conjecture3.2 in the author-repository manuscript. The original statement is broader in k. Scardino, arXiv2610.39051v1,28Oct2026, explicitly preserves the diagonal subquestion. Original proof context read: Lemma3.1 and its binomial induction, equations3.9–3.14, and Corollary3.3 proof, manuscript PDFpp7–9. They prove a truncation-error bound without assuming the conjecture; they do not settle reciprocal positivity. Scardino's body sections5–8 and Theorem8.5 compare eventual positivity with full positivity. Its c38(66,5), c37(44,7), c42(45,9) counterexamples are irrelevant to k=m.

No theorem nomination. See mechanisms.md for exact surviving routes and failures. Numerical poles or finite signs cannot prove all m,all n. We found no complete classical bridge, and did not infer novelty from that failure.
''')
put('mechanisms.md',r'''
# Sustained Padé mechanisms (auxiliary, uncredited)

1. **Reverse-Bessel recurrence.** With q0=1 and q1=1-z/2,
q_m=q_(m-1)+z² q_(m-2)/[4(2m-1)(2m-3)], m≥2.
This follows coefficientwise from factorials (the script checks m2..41 exactly; the factorial substitution gives the general identity). Put a_m=1/[4(2m-1)(2m-3)]. Then
q_(m+2)= (1+a_(m+2)z²)q_m+a_(m+1)z²q_(m-1).
The positive signs in the denominator do not become positive signs on inversion. Indeed c_(m,2)=m/[4(2m-1)] and
c_(m+2,2)-c_(m,2)=-1/[2(2m-1)(2m+3)]<0.
So both coefficientwise increasing reciprocal induction and a coefficientwise nonnegative ratio q_m/q_(m+2) fail already at degree2. This is an obstruction to those induction invariants, not to more elaborate paired induction. Direct renewal 1/q_m=1/(1-K) also has [z²]K=-(m-1)/[4(2m-1)]<0.

2. **Logarithmic/exponential positivity.** The factorial coefficients give
z q_m''+(z-2m)q_m'-m q_m=0.
For h=-q_m'/q_m=Σh_nz^n, h0=1/2, h1=1/[4(2m-1)], h2=0, and
(n-2m)h_n=Σ_(i=1)^(n-2)h_i h_(n-1-i), n≥2.
In particular [z4]log(1/q_m)=-1/[64(2m-1)²(2m-3)]<0 for m≥3. Thus exp of a nonnegative coefficient series cannot directly supply the result. The singular equation at n=2m leaves a compatibility/free coefficient issue; it is not a universal positive induction.

3. **Positive Laplace integral cannot work literally.** Already q3=1-z/2+z²/10-z³/120. Its derivative is -((z-4)²+4)/40 on the real line, so it has a unique real root R∈(4,5). The other roots are α±iβ with α=(12-R)/2<R, β≠0, and are simple. A positive measure μ on [0,∞) with 1/q3(-s)=∫e^(-st)dμ(t), s≥0, would have finite moments from derivatives at zero. For 0<x<R, monotone convergence would give ∫e^(xt)dμ=Σc_n x^n=1/q3(x), hence holomorphy for Re z<R of the moment-generating transform. But 1/q3(z) has nonreal poles α±iβ inside that half-plane. Analytic continuation from zero contradicts holomorphy. Therefore a literal positive Laplace representation is impossible, even if the target coefficients are all positive. The argument is an auxiliary classical obstruction, not a new source result. More general positive combinatorial representations are not excluded.

4. **Even-product route, exact failure beyond low orders.** Set D_m(w)=q_m(z)q_m(-z), w=z². Odd terms cancel and the coefficient formula is
d_j=(-1)^j binom(m,j) (2m-j)! m! (2m-2j)! / [(2m)!² (m-j)!].
It follows by expanding the two factorial sums; product_route.py independently checks the formula against convolution for odd m≤19. Since q_m(-z) has strictly positive coefficients, coefficientwise nonnegativity of 1/D_m would suffice for the endpoint. That stronger assertion is FALSE:
[w10]1/D_11(w)=-21866269/9888422815022969014815189447475200.
The original c_(11,20) remains positive: multiplication by q11(-z) compensates this negative term. Similar isolated negative entries occur at w^(m-1) for tested m13,15,17,19. This is a useful exact obstruction, not a source counterexample and not a count.

**Next mechanism after these failures.** Retain the even and odd numerator polynomials E_m(w)=Σω_(2j)w^j and O_m(w)=Σω_(2j+1)w^j, with ω_j=binom(m,j)(2m-j)!/(2m)!. If b_n=[w^n]1/D_m then the actual targets are Σω_(2j)b_(n-j)>0 and Σω_(2j+1)b_(n-j)>0. A useful new lemma would control negative b-blocks by their preceding positive neighbors with the source numerator weights, uniformly in m,n. For example, derive an all-order recurrence for these two weighted blocks from the displayed q recurrence, rather than falsely requiring b_n≥0. Decisive next calculation: symbolic elimination for the joint state (E_m/D_m,O_m/D_m,E_(m-2)/D_(m-2),O_(m-2)/D_(m-2)) and find a forward-invariant positive cone containing its exact initial vectors. This is a proposed mechanism; no such cone or universal block inequality is established. Enlarging the coefficient sweep will not establish it.
''')
put('SCOUTING.md',r'''
# Breadth alongside depth: primary-body triage

No discovery count. Freshness below is only relative to the bounded r213–r221 report/alias screen, not complete campaign or literature clearance. Sixteen current papers were inspected at statement level; this is not a claim of sixteen unanswered candidates or sixteen full proof audits. Thirteen are rejected/deferred quickly. New-source bodies were frozen before extraction, extraction hashed before reading, and originals/extractions checked after reading. No recursive historical copies.

## Ranked leads and reserves

1. **Fasi–Higham/Scardino, continuing odd-diagonal reciprocal Padé positivity.** Literal endpoint, original attribution and limitations are in discovery.md. Closest theorem: original Lemma3.1/Corollary3.3 handles numerator-times-exponential error without reciprocal signs; Scardino Theorems7.1/8.2 give conditional/eventual positivity. Original manuscript PDFpp7–9 and Scardino body sections5–8 read. Not fresh breadth; qualified sustained-solving lead. Exact obstructions and proposed weighted-block cone mechanism in mechanisms.md. Next step is a universal sign-preserving joint recurrence, not another finite sweep. Current complete registry head unavailable; unresolved status is explicit in28Oct2026 source, not a worldwide proof-absence assertion.

2. **Symbolic depths of edge ideals, one family with two attributed questions.** Muta–Terai [2610.39630v1](https://arxiv.org/pdf/2610.39630v1),29Oct2026, Conjecture1.1 p2 asks, for EVERY finite simple graph G, field K, S=K[x1,...,xn], and k≥1, depth S/I(G)^(k)≥depth S/I(G)^(k+1), where parentheses mean symbolic powers. Attributed there to Kimura–Terai–Yassemi Problem1.2 and Nguyen–Trung Question2.9. Conjecture1.7 p4 asks depth symbolic power≥depth ordinary power, same universal graph/field/k scope, attributed to Muta Conjecture1.6. Not split into two fresh families. Closest actual theorem:1.2 gives k→k+t when every minimal cover meets A in exactly t vertices;1.4 supplies consecutive comparison for an edge with both degrees2. Corollary1.8 proves symbolic≥ordinary only when each connected component is unicyclic or bipartite. Pages2–4 and actual local-cohomology proof pp10–11 read. **Mechanism:** enumerate minimal-cover inequalities defining Takayama degree complexes, then shift multidegrees while preserving nonzero reduced homology. **Decisive next calculation:** construct an exact obstruction certificate for the source's multidegree-shift method on leafless graphs without adjacent degree2 vertices; either find a new universal shift with a homology-surjective map, or a genuine graph/field/exponent counterexample. No assumption that graph deletion alone preserves depth. **Objection:** arbitrary field torsion and unbounded exponents remain; local results are not universal. Priority provisional; current source still calls both conjectures open, no original antecedent bodies or complete registry clearance obtained. Source1.5 stable-value question is ALREADY refuted by1.6, not a candidate.

3. **Dahlberg–She–van Willigenburg: every e-positive tree has maximum degree≤3.** Actual full statement in Tang–Wang–Wang [2610.39481v1](https://arxiv.org/pdf/2610.39481v1),29Oct2026, Conjecture1.1 p2. e-positive means all elementary-basis coefficients of the chromatic symmetric function are nonnegative. Closest theorem1.3 proves all caterpillars; source records all spiders already solved. Wolfgang connected partitions imply degree≤4, but do NOT rule out degree4; source supplies CPET degree4 families. Actual pp2–3 and Lemmas2.4–2.6 with transfer-formula proof pp5–7 read. **Mechanism:** finite-support nonnegative e-specializations, rooted-tree color-state tensor recurrences, rational invariant cones. **Decisive next calculation:** generalize the path/spine transfers to branching rooted trees and seek a cone closed under the actual branching operation while forcing negative evaluation at a degree4 vertex. **Objection:** an invariant cone for one new tree class would not solve all trees; no finite-state closure established. Famous-hard flavor and source already owns the cone route: low-priority reserve, not recommended for major investment absent a branching invariant. No narrowing to lobsters is claimed as the full conjecture. Original antecedent body and complete prior clearance still required.

## Other new-source screens (compact, no fresh/open credit)

|Primary body, exact question/scope|Closest actual statement and disposition|
|---|---|
|Easlick2610.40321v1, Conjecture1 p7: n6 is the largest n≥3 for which n-sided dice with faces in[n] admit a cycle of **maximum length n**, all edges having the parity-dependent minimum winning probability.|Theorem1 proves n6 is smallest; pp2–4 and7–9 read. Source pp8–9 explicitly displays longer-than-n cycles for n7,8,9; “maximum length n” must not be silently rewritten as absence of an n-cycle. Park scope qualification; do not call those displayed cycles counterexamples. A potential full universal max-cycle problem, not a ranked nomination.|
|Cao–Fu2610.40496v1: crown-order h* real-rooted for all r≥3.|Actual Theorems1.1/1.2 and2.1 state simple negative roots and wheel/whirl interpolation; publicly solved, exclude. Newton inequalities corollaries add no count.|
|Bowler–Pitz2610.40458v1: end-faithful/topological spanning-tree variants under countable end-degree or thin-end restrictions.|Actual Theorems1.5/1.7 give counterexamples; partial proof text for1.7 inspected. Infinite graph family, publicly resolved here; exclude.|
|Kallat2610.40342v1: restricted-permutation cycle valuations and OEIS divisibility/gcd conjectures.|Actual Theorems1.1–1.5 give valuation/residue calculus, short-cycle formulas and gcd statements. Already resolved; no relabeling one of99 sequences as fresh. Full62-page proof not audited.|
|Fiujlaali2610.40279v1: Borodin–Kostochka χ≤max(ω,Δ−1) for Δ≥9.|Actual Theorem1.1 covers (diamond,L4)-free and (diamond,K5+)-free; Lemma2.3 reduces hereditary classes to Δ9. Those classes are public results; the full famous conjecture is deferred. Not a new subclass target.|
|Lin2610.40270v1: balanced Kh-minor-free separators O(h√n).|Actual Theorem1.2 p2 claims≤min(n,21h√n), components≤2n/3. Exclude as a public proof claim pending any independent audit; no reinvention. Reading a claimed theorem is sufficient to park novelty, not to certify its correctness.|
|Atamanchuk–Briend–Donderwinkel–Herrera2610.40150v1: CRT covering-number logarithmic correction / random-tree packing asymptotics.|Actual Theorems1.3,1.4,1.6 pp2–3 identify first-order constant; Aldous logarithmic clause already refuted by Duquesne–Le Gall as explicitly stated. Analytic probabilistic family deferred, no duplication of the separate median lane.|
|Coutinho–Higino2610.40145v1: generalized theta Cartesian-product inequality and equality clause.|Actual Theorem2.1 pp3–4 proves q_k≤θ_k≤ϑ_k for real1≤k≤n, hence integral Cartesian inequality. Actual proof read via PSD Cauchy–Schwarz/lifting. Source says equality condition fails. Already public, exclude; other questions from same lifting family not split into fresh slots.|
|Chern–Nguyen–Tran–Wakhare2610.40079v1: rank3 cylindric partition bivariate identities, nonnegative c0,c1,c2 with sum3k+ε and c1,c2≤k.|Actual Theorem1.1 identifies Kanade–Russell Conjecture5.1 and gives source Ω^(ε) q-binomial factors. Publicly proved; formula scope not replaced by generic positivity. No full proof audit.|
|Milas–van Ittersum2610.40034v1, Conjectures2.7/2.8: parity-qualified root-lattice q-series (including Weyl symmetrization) quasimodular on some congruence subgroup.|Actual Theorems1.1/1.2 establish admissible level-one/two configuration results; p5 scope and pp9–10 lattice normalization read. Classical typeA and even B/C/D cases are solved. General remaining exceptional/parity cases require exact Eq2.7/2.8 definitions and new arrangement mechanism; defer rather than invent narrower solved target. No separate fresh survivor claimed.|
|Knor–Sedlar–Škrekovski2610.39966v1: connected n-vertex graph interval index≤Int(Pn), equality classification.|Actual p2 Conjecture1, p2 discussion and main theorem excerpts locate public resolution; n4 C4 exception is stated. Minimum-degree2 large-n optimum also public. Exclude, no new correction claim.|
|Brenner–Hubička–Konečný2610.39760v1: EPPA/coherent EPPA for five random-graph reducts.|Actual Theorem1.1 table classifies all five; Theorem2.2 excludes global-complement graphs. Publicly solved; exclude.|
|Ciardo–Mottet2610.40571v1: every d≥2, ε>0,k admits d-to-1 game with perfect k-compatible finite-dimensional quantum assignment but classical satisfaction<ε.|Actual Conjecture1.1 and Theorems1.3/1.4 establish d≥4 and unbounded chromatic gap. d2,3 explicitly survive p6; defer substantial PCP/quantum mechanism, not an arbitrary fresh narrowing. No solver run.|

All sixteen papers date29Oct2026 in retained version metadata. “Publicly solved” here means an actual primary theorem/proof claim supplies exclusion, not that this lane independently verified every long proof. The breadth screen is intentionally honest: three fresh reserve families after triage, not12–20 unresolved attributed statements. r213–r221 selective alias screen gives only the continuing Padé hit; it does not cover every historical alias. TRIP's seven provisionally fresh families and SCA/BHR/arborescence reserves are excluded from this lane's new tally. No accepted results claimed.
''')
put('FAILURES.md',r'''
# Failures preserved

* Initialization first used B.parents[2] instead of[3] for ancestor AGENTS and exited FileNotFoundError before scientific reading. Fixed and rerun; administrative snapshots are not scientific immutable sources.
* Guessed nhigham.com/wp-content/uploads/2020/02/fahi19.pdf returned404. No retry. Author publications page was200 but only recent entries; arXiv exact-title/author query returned zero entries; Manchester broad and exact/DOI searches did not locate a record. The distinct author-index route lawfully located record2721 and its PDF. Every response/error is retained in access.jsonl; no403/429/challenge route was attempted.
* A misplaced patch temporarily made `pages` fall through into broad body excerpts and pdftotext on its input .txt path. pdftotext exited1; original/extracted hashes subsequently all verified unchanged. Corrected control flow; no failed mathematical assertion hidden. Early large console output was truncated; later bounded page reads supplied the selected source context.
* Direct renewal kernel has negative z². Increasing order induction/ratio positivity fails at z². Logarithmic positivity fails at z4. Positive Laplace representation fails already at m3. Exact even-product reciprocal positivity fails at(m,n)=(11,10) in variable w; see mechanisms and exact fraction in product-route.json. None refutes the assigned target.
* product_route initially imported checks.py and unintentionally reran its9-second sweep. Removed that side effect; final product script is standalone. Both runs stayed within caps.
* Complete current public-registry head unavailable under allowed access; prohibited historical GitHub/ScienceDirect/Google routes were not retried. Older inaccessible history intervals remain parked. No worldwide novelty clearance.
* Only three reserve source families emerged from16-paper triage. No padding to12–20 unresolved questions, no exact dice endpoint invented from ambiguous “maximum length”, no finite-to-universal inference.
''')
put('progress.md',r'''
# Progress / handoff

2026-10-30 UTC. Counts9/39next40 administrative snapshots read. Solo assigned lane only. Immutable r220/TRIP evidence reused by path/hash, r213–r221 reports selectively screened. Original Fasi–Higham statement and surrounding actual proofs obtained from author repository, then frozen and read. Scardino diagonal preservation verified. Sixteen recent primary bodies retrieved and triaged; exact source/closest-theorem/rank/objection entries in SCOUTING.

Depth completed: factorial denominator/order recurrence, exact coefficient/logarithm obstructions, classical positive-Laplace obstruction, independent even-product route and exact counterexample to that stronger route. Source endpoint remains unresolved. The weighted even/odd numerator compensation route is the next specific calculation; no mechanism proven.

No need to formalize these helpers. No PROOF.md/Lean/manuscript; no count. Root should prioritize Padé only if a uniform compensated cone can be found; symbolic-depth and e-positive-tree leads require original antecedent/current registry clearance before sustained investment. Dice scope needs qualification before ranking. This is a research handoff, not an acceptance packet.
''')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1'/'packet'/'helper_guard.py'
put('RUN.md',f'''
# Fixed-cap replay

Every command below uses AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s in the assigned guard, without cap raises. Environment: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 (guard also pins other BLAS thread variables).

From this lane run, substituting SCRIPT with checks.py, product_route.py, report.py, finalize.py, verify.py:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python {guard} python SCRIPT`

checks.py uses exact integer-scaled coefficients and independent Fraction checks at n≤12; scope odd m≤39,n≤400. product_route.py independently convolves q_m(z)q_m(-z), checks its closed coefficient formula, then exact-inverts to w160 for odd m≤19. These bounded programs do not prove the source conjecture. checks took about9.4s and21MiB sampled groupRSS; product standalone about0.12s and12MiB. Extraction/request helpers remained well below caps. Source retrieval is optional and must respect access exclusions; no retry of denied routes. Do not rerun report/finalize after final verification without producing a new manifest/receipt.

finalize.py hashes every lane file except finalmanifest.json and verification-receipt.json. verify.py is a separate guarded invocation after writes; it checks local manifest and immutable external references and independently recomputes bounded coefficient signs and the exact even-product obstruction. Receipt records verification outcome and manifest hash; it is intentionally outside its manifest.
''')
refs=json.loads((L/'references.json').read_text())
put('provenance.json',json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':{'additional':9,'total':39,'next':40},'status':'HOLD_NO_COUNT','reference_manifest':'references.json','reference_count':len(refs),'access_log':'access.jsonl','administrative':'snapshot only; source changes not treated as corruption','source_policy':'scientific sources frozen before reading; originals and extraction immutable; no recursive history duplication','original_source':{'url':'https://eprints.maths.manchester.ac.uk/2721/1/fahi19.pdf','doi':'10.1137/18M1228876','statement':'Conjecture3.2 printedp8 PDFp9; surrounding proof PDFpp7–9','sha256':hashlib.sha256((L/'sources'/'fahi19.pdf').read_bytes()).hexdigest()},'chronology':['Fasi–Higham2019 original broad conjecture','Scardino28Oct2026 off-diagonal refutation and explicit diagonal survival','breadth bodies29Oct2026','this lane30Oct2026 UTC'],'limits':['No complete current public proof-registry head','No original antecedent bodies for breadth reserves','No publisher-version collation of author manuscript','No worldwide novelty claim','No all-m/all-n proof','Selective history/alias scan only; parked inaccessible intervals not reopened'],'forbidden_actions_performed':False},indent=2))
print('reports written')
