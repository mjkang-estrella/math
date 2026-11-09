from pathlib import Path
import json,hashlib,math,datetime
D=Path(__file__).parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r579'
def J(p):return json.loads(p.read_text())
def W(p,x): (D/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
notes={
390759:'The {n,2n,3n} constraint decomposes over 2,3-smooth multiplicative components, but a limiting series alone would not decide irrationality. No full value-plus-irrationality route.',
390761:'Difference counting gives only a square-root lower bound; block constructions only upper constants. Neither determines the requested limiting constant.',
390773:'No-average-of-any-number restriction is stronger than three-term progression avoidance. A progression-free construction would not settle its growth order.',
390774:'Van der Waerden existence for each fixed length gives no optimal rate as a function of the common difference. No matching rate mechanism.',
390775:'A periodic colouring would need certification for every orientation of unit-step progressions and a matching impossibility bound for smaller k. Neither supplied.',
390776:'Rainbow progression length is not specified literally; if length two were allowed the intended extremal problem changes. Restore primary length convention before asymptotic work.',
390783:'The statement does not explicitly define G as the largest guaranteed size; even with that intended convention, interval bounds alone cannot establish the ratio for arbitrary N-element integer sets.',
390793:'Finite coordinate witnesses address individual n only; complete characterization requires both general constructions and impossibility outside the range. No such route.',
390797:'A CRT construction yields some large gaps but does not settle the broad request for good upper and lower bounds. No sharp full-scope endpoint specified.',
390798:'Planar diameter arguments address d=2 only. All dimensions require separate extremal geometry; a small configuration cannot determine M_d(n).',
390812:'Counting unordered triples gives a nonsharp constant; an algebraic B_3 construction supplies only one side. Matching leading constant not obtained.',
390842:'For a fixed finite modulus list one can enumerate residues modulo the lcm, but that algorithm neither supplies a general optimal formula nor proves the asserted aligned minimum for every list.',
390856:'Exact subset-sum dynamic programming after multiplying by lcm(1,...,N) is finite but grows rapidly and does not determine the exponential asymptotic rate.',
390859:'The upper half interval has reciprocal sum below one and hence gives a linear construction, not density 1-o(1). The asserted near-full density needs a different global argument.',
390860:'Putting all denominators in a short multiplicative interval does not prevent sums of arbitrarily many reciprocals. No full asymptotic upper/lower pair.',
390861:'For reciprocal triples, scaled identities generate forbidden configurations, but a finite hypergraph independence computation cannot certify the all-N leading density.',
390883:'The choice a=1,b=n-1 gives a trivial smoothness bound, not the best uniform function. Obtaining optimal smooth decompositions is not a bounded certificate problem.',
390905:'The optimization depends on both real c and integer n; avoiding one subset sum is not answered by a single modular construction. Irregularity clause also lacks a precise endpoint.',
390911:'Literal question omits whether size means pointwise, typical, liminf, or infinitely often. Primary quantifier restoration is necessary; no theorem inferred from the broad wording.',
390913:'Exchanging n and n+1 is not a density-preserving symmetry of largest prime factors. No valid involution or error estimate proves density one half.',
390922:'CRT can force divisibility by selected small primes but not certify the largest prime of the entire interval product repeats. Both subpolynomial length and unbounded length need separate arguments.',
390937:'Prime-valuation feasibility is computable for each n, but average and almost-all logarithmic asymptotics need uniform carry/prime information. Factorial domain must be nonnegative.',
390944:'Iterating phi for bounded n cannot certify distribution or concentration; nonintegral k=log log n also requires a rounding convention from source.',
390972:'Residue classes avoiding square sums provide lower bounds only. The exact maximum for every N needs a global upper bound; no full route.',
390980:'Finite inclusion-exclusion on moduli gives exact densities at fixed N but not their asymptotic order or the ratio of exactly-one divisors. Two distinct endpoints retained.',
390988:'Smooth-number enumeration for fixed u,v does not bound the largest permissible v uniformly as u varies. Interval endpoints and common prime support remain coupled.',
391000:'The index i in q_n+q_i-1 is not bounded explicitly. Under the intended previous-index convention, computing a long prime chain does not prove it continues indefinitely.',
391007:'The sqrt2 recurrence can be checked exactly using integer square roots. Agreement of its first 64 extracted bits gives no analogue for every sqrt(m) or other algebraic numbers; such an analogue also needs a precise allowed recurrence class.',
391022:'This is the full (3,4) hypergraph Turan extremal function. Small-n enumeration or the usual cyclic three-part construction supplies no all-n matching upper bound.',
391024:'Two-distance sets are sufficient but are not all isosceles sets. A two-distance construction or low-dimensional classification does not determine the maximum in every dimension.',
391025:'Regular polygon constructions provide upper examples, but a universal angle lower bound and equality characterization require separate geometry. No primary proof body inspected.',
391028:'The phrase let alpha(n) be such that is not an extremal definition; any larger bound also works. Intended smallest universal bound must be restored; finite area searches do not resolve its asymptotics.',
391029:'Finite unit-distance graphs certify lower bounds, and periodic colourings upper bounds; no matching full-plane colouring/lower obstruction obtained.',
391045:'Submultiplicativity can establish existence of a connective constant, not its value for all lattice dimensions. Finite walk counts cannot determine C_k exactly.',
391047:'Greedy removal gives a nonsharp guaranteed Sidon subset; random embeddings/constructions alone do not determine the universal worst-case order.',
391051:'The compulsory element N restricts possible entries to its noncoprime neighbours, but their pairwise compatibility depends on additional shared factors. No uniform exact extremal formula derived.',
391052:'Excluding r-tuples with a common pairwise gcd is an all-subset condition. A fixed-gcd or fixed-prime construction does not provide matching full-r asymptotics.',
391065:'C4-free degree bounds relate the star Ramsey problem to extremal graphs, but isolated polarity constructions do not settle all n or the arbitrarily large deficit c.',
391068:'Two-colour even-cycle results or fixed k do not determine all multicolour parameters. No uniform exact formula route.',
391071:'Star and balanced bipartite special cases leave general s,t,k unresolved. A finite Ramsey computation supplies parameter instances only.',
391073:'Choosing a complete host gives a crude upper bound for size Ramsey number. Optimizing over every host needs a matching lower bound absent here.',
391089:'Cube embeddings for a fixed k do not determine Turan behaviour for every k. No matching extremal upper/lower mechanism.',
391093:'A random cut guarantees e/2, but the question asks the order of the excess above it in triangle-free graphs. That routine bound is not an answer; cited Alon proof body not read.',
391096:'The metadata points to a 2025 journal article, which is a material successor lead, not proof-body clearance. ScienceDirect route prohibited; no fetch or claim of public resolution.',
391098:'Avoiding squares elementwise is weaker than forbidding every nonempty square subset sum. Residue constructions alone do not yield a matching growth order.',
391103:'Without ordered copies every countably infinite complete graph reduces to the countable Ramsey theorem; intended ordinal order type must be restored from primary source. Pinned GitHub route prohibited.',
391119:'The O(1) constants and allowed r,d domain are not explicit. Layer counting would need clique-sensitive optimization with the exact coefficients; no such proof or legitimate counterexample.',
391121:'Complementation turns the local maximum-degree condition into a forbidden induced configuration, but this does not yield the sharp all-n,k extremal function. Small k earns no credit.',
391123:'For r>=3 two disjoint edges fit inside 3r-3 vertices, so the hypothesis forces pairwise intersection and trivially tau<=r by selecting one edge. That upper bound alone does not determine best t or sharp examples.',
391133:'Actual v2 source body gives limsup g=M^2 and liminf g>=L^2; Theorem1.2 yields convergence only assuming Conjecture1.1 and a diagonal Ramsey limit. Neither assumption is discharged. Improving its numerical bound is already covered by Theorem1.3 and earns no full-scope result.'}
rows=[]
rest={390776,390783,390911,390937,390944,391000,391007,391028,391103,391119}
for a in J(D/'literal-records.json'):
 r=a['record'];i=a['id'];s=r['statement'];rows.append(dict(mathdb_id=i,chunk=a['chunk'],line=a['line'],statement=s,statement_utf8_sha256=hashlib.sha256(s.encode()).hexdigest(),canonical_record_sha256=a['canonical_record_sha256'],source_url=r['source_url'],first_stated_year_source_url=r['first_stated_year_source_url'],scope_flags=dict(cached_label=r['statement_completeness'],literal_statement_read=True,self_contained_scope_confirmed=False,primary_restoration_required=i in rest,all_parameters_required=True,parameter_instances_earn_credit=False),disposition='HOLD_SCOPE_RESTORATION' if i in rest else 'HOLD_NO_FULL_SCOPE_ROUTE',technical_disposition=notes[i],evidence=dict(statement='complete literal record',selected_primary_passage=i==391133,whole_primary_body_read=i==391133,local_proof_read=i==391133,full_dependency_audit=False,successor_clearance=False,current_registry='HOLD unavailable; zero requests'),accepted_credit=0,prior_cleared=False))
W('dispositions.json',rows);W('proposals.json',[])
a=[0,1]
for _ in range(130):a.append(math.isqrt(2*(2*a[-1]+1)**2)//2)
checks=[dict(n=n,recurrence_bit=a[2*n+1]-2*a[2*n-1],sqrt2_bit=math.isqrt(2*(1<<(2*n)))%2) for n in range(1,65)]
W('bounded-checks.json',dict(id=391007,executed=True,method='exact integer sqrt; no floating point',range='n=1..64',all_match=all(x['recurrence_bit']==x['sqrt2_bit'] for x in checks),checks=checks,limit='Validation of the stated example only; not a proof or generalized recurrence. No further sweep planned.'))
look=J(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json')['mathdb_lookup'];matches={str(a['mathdb_id']):look[str(a['mathdb_id'])] for a in rows if str(a['mathdb_id']) in look}
W('prior-context-check.json',dict(r304_lookup_matches=matches,required_inputs_bound=True,r363='364119 source-adaptation exclusion persists',r579='adjudications and hypothesis queue read; no reopening',scope_restoration_preserved=[344924,386396,387650],other_protected='No assigned IDs are protected; 366370 exclusion, stack-fiber parks, and 372522 proof-gap distinction preserved',counts=dict(additional=9,total=39,next=40),promotion=False,registry='HOLD unavailable, no absence-of-hits inference'))
W('source-coverage.json',dict(record_reviews=50,baseline_record_reviews=5433,prospective_root_reconciled_record_reviews=5483,baseline_not_complete_math_statements=True,primary_selected_passage_rows=[391133],whole_body_rows=[391133],local_proof_rows=[391133],full_dependency_audit_rows=[],successor_clearance_rows=[],registry_clearance_rows=[],body_limit='arXiv v2 sections1-3 and references read as extracted text; external cited Ramsey proof bodies not read or verified; numerical optimization not independently certified',all_other_rows='literal statement only; metadata source links not primary body evidence',proposals=0))
W('failures.json',dict(access_failures=[],failed_calculations=[],stopped_routes=['No sharp constant route for multiplicative/additive extremal records','391007 finite recurrence check stopped before generalized algebraic recurrence search','391133 conditional theorem does not settle unconditional limit; no numerical-bound adaptation pursued'],deviations=['Queue head displayed several scientific titles before initial binding during schema inspection. No dispositions were made from these titles; full literal statements read after binding.','Initial full-record tool output truncated; replaced by complete statement-only output for all fifty before screening.'],parked=['MathDB 429 zero requests','proof registry unavailable HOLD','OEIS A274199/internal HTTP403 from r542 no retry','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate403','Google/GitHub/API/raw/codeload/diff/ScienceDirect/browser/preview/TLS bypass'],upstream_verify_executed=False))
print('50 individual dispositions; proposals 0; exact recurrence check',all(x['recurrence_bit']==x['sqrt2_bit'] for x in checks),'r304 matches',matches)
