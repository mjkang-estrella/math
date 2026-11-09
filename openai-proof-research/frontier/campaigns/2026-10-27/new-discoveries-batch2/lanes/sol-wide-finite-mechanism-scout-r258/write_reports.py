from retrieve import *
def write(name,s):(L/name).write_text(s.strip()+'\n')
write('PROOF.md',r'''
# Odd-characteristic full refutation; eligibility HOLD

This is a mathematical refutation of Chapman–McGuire, arXiv:2102.02081v1 (3 February 2021), Section 3 Conjectures 1 and 2, one family only. It is not a novelty clearance or an accepted outcome. Independent mathematical/source/substantive review is required. No Lean or manuscript was made.

## Literal source scope

The source introduces any prime power q, n>=4, and 1<d<n dividing n. For x in F_(q^n), alpha=x^(q^d-1), R_d(x)=x+x^q+...+x^(q^(d-2))+x^(q^(d-1)+q^d-1). Section 3 works with alpha not 0 or 1 and with the denominators in Eq(12) nonzero. Eq(12) is

 (1-alpha^(q+1))/(1-alpha^(q+1))^(q^d)
   = alpha^(1-q^(d-1)) (1-alpha)/(1-alpha)^(q^d).

Eq(13) is alpha^((q^n-1)/(q^d-1))=1. Conjecture 1 says that for d=2 Eq(12) implies alpha^(q+2)=1. Conjecture 2 adds Eq(13). The final remarks specify even n. We satisfy the stronger actual R_d(x) condition as well as both equations, with odd q and even n; no excluded characteristic or missing-source hypothesis is exploited.

## Route A: direct field certificate

All following polynomials have coefficients in F3. Put

 g(Z)=Z^7+Z^6-Z^4-Z^2-Z-1.

This polynomial is irreducible. Here is a short reproducible certificate, rather than a numerical irreducibility assertion. The successive residues of Z^(3^i) modulo g for i=1,...,7 are:

 Z^3;
 -Z^5-Z^4+Z^2+1;
 Z^6+Z^5+Z^4+Z^2+Z+1;
 Z^6+Z^5-Z^4+Z^2+Z+1;
 Z^6+Z^5-Z^4+1;
 Z^5-Z^4-Z^3+1;
 Z.

Each line is obtained by cubing the previous line and substituting Z^7=-Z^6+Z^4+Z^2+Z+1. Also g(0)=2,g(1)=1,g(2)=1. Since g divides Z^(3^7)-Z, each irreducible factor has degree dividing 7. Since 7 is prime and g has no linear factor, g is irreducible. This uses the standard finite-field factorization of X^(p^m)-X; it is not a bounded search for a conjecture witness.

Let K=F3[Z]/(g), and x be the class of Z. Then K is F_(3^7), embedded in F_(3^14) because 7 divides 14. Set q=3,n=14,d=2 and alpha=x^8. The identity

 Z^11+Z+1 = g(Z)(Z^4-Z^3+Z^2-1)

gives R_2(x)=x+x^11=-1 in F3. In particular, the original curve condition holds. The element x is nonzero, because g(0) is nonzero. Its minimal polynomial has degree 7. Therefore alpha is not 1 (otherwise x is a root of Z^8-1 and, more specifically, alpha's explicit degree-six residue below rules this out). Direct reduction gives

 alpha=-1+x^3-x^4+x^5+x^6,
 alpha^5=-x^6+x^5-x^4-x^3-x^2+x-1.

Both alpha-1 and alpha^5-1 are nonzero polynomials in x of degree below 7. Consequently alpha!=1 and alpha^(q+2)!=1. Further alpha^4!=1: otherwise alpha^5=alpha and the difference of these two displayed residues would vanish, which is a nonzero polynomial of degree below 7. Thus U=1-alpha^4 and V=1-alpha are nonzero, proving every denominator in Eq(12) is defined.

It remains to check the displayed equations, without relying on the source's converse in Theorem 3. Write R=x+alpha*x^3. Because R is in F3, R^3=R. Since x^9=alpha*x, this yields

 x(1-alpha^4)=x^3(1-alpha), hence U=x^2 V.

Raising to the ninth power gives U^9=x^18 V^9=alpha^2*x^2*V^9. Division is valid, and U/U^9=alpha^(-2)*V/V^9, exactly Eq(12) at q=3,d=2. Finally

 alpha^((3^14-1)/8)=x^(3^14-1)=1

because x is a nonzero element of F_(3^14). This is Eq(13). All source hypotheses hold, while the conclusions of BOTH conjectures fail. Two conjectures receive only one possible family credit. This does not classify all bonus points or all q,n,d.

## Route B: the alpha-polynomial mechanism

Starting from the source's Eq(6) at d=2, put T(A)=1+A+A^2+A^3. Requiring x^2=T(alpha) and alpha=x^8 reduces the compatibility obstruction to T(alpha)^4=alpha. In F3[A] there is an exact factorization

 T(A)^4-A=(A-1)(A^4+A^3+A^2+A+1)
             (A^7+A^6+A^5-A^4+A^3-A^2-1).

The first two factors are the expected fifth roots; the degree-seven factor is additional. It is irreducible by the prime-degree Rabin test, and coprime to A^5-1 and A^4-1 (checks.py records exact modular tests). A root alpha lies in F_(3^7), and a square root x of T(alpha) exists in F_(3^14). Then x^8=alpha. From x^2(1-alpha)=1-alpha^4 one obtains R^3=R directly, and the same division above gives Eq(12), with Eq(13) automatic. This independent parametrization explains why increasing n can expose components invisible in the source n=6 analysis.

Elimination gives the independent x-polynomial Z^14-Z^12-Z^10-Z^8-Z^2-1, whose degree-seven factors include g above. Route A verifies the chosen component without needing any assertion about the other component. SymPy elimination and an independent integer-tuple F3 quotient implementation agree on every literal equation; the proof is the displayed identities and field argument, not the checks alone.

## Nearest actual source proof and novelty objection

Theorem 3's derivation of Eqs(5)–(12), Section 3 pp4–5, was read. Theorem 4 handles d=n/2; Section 6's n=6 resultants and Lemmas 18–19 explicitly restrict to odd q and the final remarks describe Theorem 20 as the n=6 case. Our n=14 is outside both restrictions. The argument does not contradict those scoped results. The source's Fibonacci gcd remark is a different question, not a second discovery.

The strongest substantive objection is that adjoining a root of T(A)^(q+1)-A to a sufficiently large finite field is a short classical finite-field bridge from source Eq(6). This is not itself grounds to reject a full source resolution, but it must be adjudicated independently: the degree-seven extra component and its compatibility with an actual x, Eq(13), nonzero denominators, and odd characteristic are the concrete additional work. No theorem is claimed new to the literature. Current complete public registry heads and specialist citation bodies remain uncleared. HOLD.
''')
write('SCOUTING.md',r'''
# Thirteen attributed source-question families

2026-10-30. Counts remain 9 additional / 39 total / next 40. These are thirteen screens, not thirteen certified-open nominations. Versioned primary PDFs were frozen and hashed before text extraction. URLs are exactly https://arxiv.org/pdf/ followed by the identifiers below. selected.json supplies authors, first-submission and latest-version UTC dates; primary-sources.json binds PDF/text hashes and locations. Metadata discovery slices span 2020 combinatorics, 2021 arithmetic and 2022 algebra. Three extra algebra papers with no sufficiently precise question were read but NOT counted (2202.02127, 2202.11826, 2202.12026).

Early exact-ID and semantic campaign-alias checks over 888 immediate historical reports found no listed hits; history-hits.json records the bounded terms and history-bindings.json the in-place hashes. This is not exhaustive semantic clearance. Excluded active analytic r257, floor, retired commuting-spectrum/triangular-polarization, supercoupon, spectral-energy, two-defect and ternary80 families were not reopened. Two earlier scout reports were read only to enforce exclusions; no historical trees were copied.

## Ranked survivors (only two)

1. Chapman–McGuire, 2102.02081v1, 3 February 2021, Section3 Conjectures1–2, pp4–5. For every permitted prime power q, even n>=4, d=2 dividing n, and actual alpha=x^(q²-1) in F_(q^n), Eq(12), even with norm Eq(13), is claimed to imply alpha^(q+2)=1. **Full mathematical refutation found, eligibility HOLD**: q3,n14 and an exact degree-seven field certificate. PROOF.md proves all original hypotheses and the actual R_2(x) condition in two distinct algebraic routes. Nearest actual proof: Theorem3's Frobenius derivation, Theorem4 d=n/2 and Section6 n=6 resultants; none covers n14. Decisive next action: independent verification of the source scope, exact proof and substantive classical-adaptation objection, then current public-registry/prior-art closure. New mechanism here: the extra degree-seven component of T(A)^4-A, compatible with an actual x and the norm condition. Strongest objection: short classical extension-field construction from Eq(6). No novelty PASS is inferred from a conjecture label or empty solutions. Current exact-author/title arXiv follow-up queries return only source v1; OpenAlex matched source has zero indexed citers, which does NOT clear prior art.

2. Evans–Greene–Van Veen, 2002.02550v1, 6 February 2020, introduction p2 and Section9 pp31–32. For all even n>k>=1, ord_(x=0)det A(n,k,x)=nullity A(n,k,0); first k superdiagonals are1 and the rest -x, with skew transpose. **Unresolved research lead, not a proof.** Actual Theorem9.2 proof uses D=F_(n-k-1)^2 and recurrence F_(a+2)=(x+1)F_(a+1)-F_a in k>=(n-2)/2. The remaining k<=(n-4)/2 does not inherit that determinant formula. Mechanism route: restrict the derivative skew form to the exact source kernel. A congruence split into kernel and invertible block gives the leading determinant coefficient as a nonzero scalar times det of that restriction. Missing lemma is its nondegeneracy uniformly in n,k. Independent row-difference route: for a zero-padded vector v and s=1+x, differences of consecutive A(n,k,x)v rows are s(v_(i+k+1)+v_(i-k))-v_i-v_(i+1); interior recurrence and BOTH boundary blocks are essential. No uniform boundary determinant was proved. Decisive next calculation is a symbolic source-cycle basis pairing, not an expanded finite sweep. Strongest objection: a known Pfaffian/Toeplitz pencil identity may subsume the restriction lemma; source2019 Evans–Wallach body remains unread and no current registry head is available. Current targeted arXiv query finds source only, not novelty clearance.

## Compact non-survivors

3. Mynhardt–Ogden, 2002.01347v1 (3 February2020), Conjecture1 p19: for every total-Roman edge-supercritical graph G and every vertex v, some minimum total-Roman dominating function is positive at v. (Conj2 disjoint-clique consequence is the same family.) Actual Prop4.4 repairs corona nonedges explicitly; Prop10.4's listed functions prove the Gr family only, and Cor10.5 uses exactly that support fact. Missing universal step is repairing a minimum function on G+vw at total cost2 while keeping v positive; a new positive vertex can be isolated after removing vw. Park; no universal repair or counterexample. Strongest classical objection: existing domination criticality lemmas may already supply the support property. Retrieved direct predecessor1907.08639 is a lead only, not body-cleared; no claim of a new result.

4. Gabric–Shallit, 2002.01968v2 (25 February2020), Section5 p10: is Theorem6's bound for C(k,n), the maximum length with no two disjoint occurrences of the same length-n factor, tight or asymptotically tight beyond n<=3? Actual Lemma5/Theorem6 proof counts each factor at most ceil(n/per(w)); summing gives C<=sum_(w in Sigma_k^n)ceil(n/per(w))+n-1. Individual attainability in Lemma5 does not establish simultaneous attainability. Park: need a de Bruijn-type trail whose repeated short-period factors overlap in compatible windows. No square-reduction/ternary80 target is involved and no source example is offered as a discovery.

5. Milich–Mütze–Pergel, 2002.02290v3 (9 October2020), Section7 p24: is diam H_n=3n-7 for every odd n>=3, where H_n uses only centered quadrilateral flips between noncrossing perfect matchings of regular2n points? Actual Theorem8 full path proof gives n-1<=diam<=11n-29, reaching a perimeter matching in4n-11 flips and joining the two perimeter matchings in3n-7. Missing global geodesic/layer bound; source computational cases through11 do not prove it. Park: define a layer statistic with rigorous one-step constraints AND an all-pairs canonical path. Same paper's solved Narayana enumeration not nominated.

6. Semonsen, 2002.02482v2 (10 February2020), concluding discussion pp8–9: for every n,k with k ones in each row, is the maximal absolute0-1 determinant unchanged on requiring k ones in each column? Actual LP block proof/Lemma2.7 optimizes block counts and the final discussion constructs row/column-regular examples but explicitly retains Fischer volume loss between block sizes. Missing optimum-preserving balancing operation. Park: a finite strict inequality with exact maxima would refute the general assertion; determinant sweeps without certified column-regular upper bounds cannot. No projective-plane block concatenation nominated.

7. Just–Schneider, 2102.00944v2 (9 April2021), pp2–3: partition all NE(n,n) paths into2n-1 equal classes distinguished by area modulo2n-1. **Already answered in this source**. Actual Section3.1 rotation proof keeps the first step fixed, rotates the remaining2n-1 positions, and changes area by n-1 or n modulo2n-1, both units. This proves exact orbit size and equidistribution. No gap remains in this scoped question; no new orbit argument proposed. Noncoprime generalizations are not silently counted as open variants.

8. Spiegelhofer, 2102.01018v2 (18 November2021), Shallit's gap question: for a factor w of the Thue–Morse word of length>=2, is the sequence of successive occurrence gaps automatic? **Already answered negatively in source Theorem1.1.** Actual Section2 builds the abc/ac/b morphism and reduces arbitrary factors to01; the automatic occurrence-indicator theorem is distinct from automaticity of gaps. Full source section read in bounded proof-read log; no new nonautomaticity result. The original question was workshop/private communication, not a separately retrieved publication.

9. Delaygue–Rivoal, 2102.01534v2 (6 August2021), Conj2 pp3–4: every integer sequence with a_(n+p)=a_n modp for all n>=0 and prime p, and limsup |a_n|^(1/n)<e, is polynomial in n. Actual Theorem1 binomial-transform proof requires primorial divisibility and gives only the e-1 bound; Theorem2 uses algebraicity, and Theorem3 gives a polynomial-coefficient recurrence. Neither algebraicity nor polynomiality follows from recurrence alone. Park famous-hard core (Ruzsa/Christol/van der Poorten bridge), no new mechanism; not a finite congruence-search nomination.

10. Gjaldbæk, 2102.03392v1 (5 February2021), irrational-sector quadratic packing question posed in introduction: can a quadratic integer-valued polynomial biject S(alpha) intersect Z² onto N0 for irrational alpha>0? **Already answered by same source Cor6.** Actual Theorem2 proves noninjectivity for nonzero discriminant by rational symmetric lattice pairs; Theorem5 integrates the zero-discriminant quadratic density and forces alpha=A/(1-B), rational. Both source proof bodies inspected. This does not settle the famous all-degree Fueter–Pólya question; that hard extension is not nominated.

11. Booker–Cohen–Leong–Trudgian, 2202.00829v1 (2 February2022), Gupta–Sharma–Cohen primitive-pair question: for every n>=3 and prime power q outside(3,3),(4,3),(5,3), every prescribed trace is realized by primitive xi with xi+xi^-1 also primitive. **Already answered in source Theorem1.1.** Actual Section2.1 modified-prime-sieve reduction and Section2.2 explicit cubic/norm lemma plus symmetry and residual computation were read. No rerun of the multi-day computation, certification of all published computation, or new existence theorem is claimed. Original predecessor question body not separately retrieved, so this is exclusion by the explicit source proof, not an original-priority audit.

12. Sriwongsa–Zou, 2202.01333v2 (12 February2022), Section3: is every finite group the automorphism group of some finite-dimensional idempotent evolution algebra over each characteristic-zero field? **Already answered in source Theorem3.1.** Actual proof takes Frucht's graph, chooses a nonsingular B+mI, kills the diagonal automorphism subgroup via its nonzero diagonal, and identifies the permutation subgroup. No characteristic-zero gap remains. Positive-characteristic uniform realization would need separate hypotheses and is not manufactured here.

13. Cooper–Hanna–Whitlatch, 2202.04012v1 (8 February2022), Section6 p12: polynomial-time decision of whether a pseudo-graph over a finite field admits some successful pressing order. Actual Theorems2–4 and appendix LDU argument characterize a FIXED order by positive leading pivots over definite fields; Theorem6 supplies counterexamples to several Hermitian analogies. Missing search-order theorem: eliminating one permissible positive pivot may destroy others, and symmetric quadratic-form congruence allows basis changes beyond source vertex permutations. Park; a pivot-order algorithm requires an exchange theorem or complexity reduction. No one-line Gaussian-elimination bridge is complete. Field-size encoding and nondefinite-field scope need precise clarification before full algorithm investment; no formulation-correction credit.

## Access limits

No current GitHub registry head was obtained. Inherited API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not retried; no browser, proxy, TLS bypass or external mutation. Narrow current arXiv searches and OpenAlex metadata are only bounded leads. No inaccessible historical HEAD loop. Resolved-source exclusions above do not assert all original predecessor bodies were retrieved or certify external computations. Unread predecessors remain explicit gaps rather than novelty PASS. No accepted/rejected campaign family was knowingly re-nominated.
''')
write('SUMMARY.md',r'''
# Research handoff — r258

Thirteen distinct attributed finite/arithmetic/algebraic source-question families screened from versioned primary bodies. Two ranked leads; no fabricated third. Best result: a complete odd-characteristic counterexample to Chapman–McGuire2102.02081v1 Conjectures1–2, one family. Take q=3,n=14,d=2 and x a root of Z^7+Z^6-Z^4-Z²-Z-1 in F_(3^7) embedded in F_(3^14). Then R_2(x)=-1, alpha=x^8 satisfies source Eqs12–13 with nonzero denominators, and alpha^5!=1. Two exact algebraic routes and independent integer-tuple verification support the written proof.

**Eligibility HOLD, independent review required. No new-to-literature or acceptance claim.** Short classical finite-field adaptation is the strongest substantive objection; current complete proof registries are access-blocked and specialist prior-art closure is incomplete. Root alone adjudicates/counts. Counts unchanged:9 additional,39 total,next40. No Lean, manuscript, shared files, git, browser, MathDB edits, public posting or children.

Read PROOF.md and discovery.md first, then SCOUTING.md. The second lead is the general Toeplitz-pencil multiplicity statement, with explicit missing kernel-pairing and boundary-recurrence lemmas. final-manifest.json excludes itself and final-verification.json; the latter is a separately guarded post-write verification receipt.
''')
write('discovery.md',r'''
# Discovery status and sustained work

MATHEMATICAL FULL REFUTATION of the literal source Conjectures1–2 in one twisted-trace family; ELIGIBILITY HOLD. PROOF.md contains all quantifiers, source hypotheses, exact certificates and two distinct routes. This is a research proof note, not a manuscript or formalization.

Route1 starts from a direct degree-seven irreducible field polynomial and proves the original R2 condition, Eqs12/13 and failure of alpha5=1. Route2 starts from the source's x²=T(alpha), detects the additional degree-seven factor of T^4-alpha beyond the expected fifth roots, and constructs the compatible x in a quadratic extension. The final direct witness already lies in the degree-seven subfield. Neither route is an unstructured finite sweep. The q2 witness was considered first, then deliberately superseded by odd q3 to avoid relying on a characteristic exception in the source's n6 proof. No q2 outcome or separate credit is proposed.

The original Toeplitz lead was pursued by symbolic kernel-block Schur complement and the independent row-difference recurrence; no nondegeneracy lemma was found. It remains rank2, not a theorem. The bounded arXiv source/follow-up and original campaign alias checks preceded significant solving. Later targeted exact-author/title queries and OpenAlex citation metadata did not locate a follow-up resolution, but do not clear current proof registries. Inherited denied paths were not retried.

Strongest remaining objections: (1) actual prior resolution in currently inaccessible registries or specialist sources; (2) routine-corollary/substantive status of the finite-field extension bridge; (3) independent validation of the source's intended all-even-n quantifier. Our odd-q14 example satisfies all printed source hypotheses, so it does not depend on extending an n6 theorem or on a missing denominator. Root should request independent source/mathematical review before any formalization. No claim about earliest priority or original curve point-count classification.
''')
write('progress.md',r'''
# Progress

1. Administrative ancestor/batch rules, ledger and prior context snapshotted; counts9/39/next40 retained.
2. Pinned source catalogue and scout exclusions frozen; history indexed in place (888 reports, exact hashes), no recursive archive duplication.
3. Dated discovery slices and 16 versioned primary PDFs retrieved; 13 question families retained for breadth, three no-question algebra probes not counted.
4. Actual source questions and relevant proof sections read. Five families rejected because the inspected source already answers the scoped question; others parked behind explicit mathematical gaps.
5. Toeplitz kernel-form and recurrence routes developed, unresolved. Twisted-trace algebra isolated an extra degree-seven component; odd-q direct field certificate completed by two routes.
6. SymPy exact polynomial checks and independent tuple arithmetic agree. Failed import, retrieval failures and deprecation warning preserved in failures.md. No cap increases.
7. Independent review, full current prior-proof registry closure, and substantive eligibility remain HOLD. Root alone accepts/counts; no shared state changed.
''')
write('failures.md',r'''
# Preserved failures and bounds

- Initial /list/math.CO/2002 request returned a historical listing (year2002), not the intended February2020 slice. Retained and not used as mathematical evidence. /list/math.NT/2102 and /list/math.RA/2202 returned404; retained in retrieval.jsonl. Corrected to API date queries.
- Two API date ranges incorrectly ended in February29 for2021/2022 and returned500. Corrected once to valid February28 dates. These were input corrections, not retries of403/429/challenges. No denied route was retried.
- First trace_test.py import failed because lane inspect.py shadowed stdlib inspect, causing ImportError: cannot import name getmro. Renamed under guard to inspect_bodies.py; exact subsequent checks pass. No numerical or scientific result was produced by the failed run.
- SymPy factor_list produced the modular-integer-ordering deprecation warning. Results were independently checked by ordinary integer tuple arithmetic; no tolerance or numerical minimum is involved.
- Some initial combined tool outputs were truncated. Bounded targeted reads were subsequently used for the relevant source statements and proof bodies. No claim of entire historical-report or entire 719-manuscript reading.
- No current complete GitHub registry head, original Evans–Wallach2019 body, exhaustive specialist citation audit, or MathSciNet/zbMATH access. API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were inherited denied and stayed parked. OpenAlex zero indexed citations is not a proof of absence.
- No proof of the Toeplitz kernel restriction's nondegeneracy, Roman minimum-support repair, or pressing-order exchange. Those failures remain gaps, not inferred universal results.
- All Python/helpers/retrieval/hash/edit operations were launched through the assigned fixed helper_guard with OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1. Native bounded reads and apply_patch were used as authorized. Fixed AS/groupRSS512MiB,CPU210s,wall230s; no raises. Each launch's guard record is in tool history; scientific check summaries are in checks.json and independent-checks.json.
''')
sources=[]
for j in json.loads((L/'selected.json').read_text()):
 ident=j['id'].split('/')[-1];p=L/'sources'/(ident+'.pdf');t=L/'sources'/(ident+'.txt')
 if p.exists():sources.append({**j,'url':'https://arxiv.org/pdf/'+ident,'pdf':str(p),'sha256':sha(p),'text':str(t),'text_sha256':sha(t)})
(L/'primary-sources.json').write_text(json.dumps(sources,indent=2))
(L/'provenance.json').write_text(json.dumps({'date':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':{'additional':9,'total':39,'next':40},'acceptance':'root only','scientific_bindings':'bindings.jsonl','new_primary_retrievals':'retrieval.jsonl','immutable_history_references':'history-bindings.json','current_registry_head':None,'registry_limit':'inherited denied routes parked, no retry','novelty':'HOLD','math':'full source refutation pending independent review','lane_only':True},indent=2))
print('reports written',len(sources),'primary PDFs;13 screened families')
