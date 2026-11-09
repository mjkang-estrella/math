import json,re,pathlib,hashlib
H=pathlib.Path(__file__).resolve().parent
prov=json.load(open(H/'literal-provenance.json')); res=json.load(open(H/'reservation.json'))
hist=[l.rstrip('\n') for l in open(H/'history-search.txt',errors='replace')]
rec=[json.loads(l) for l in open(H/'receipts.jsonl')]
def receipts_for(arx): return [r for r in rec if arx and arx in r['url']]
SO='statement_only_literal_and_bounded_history'
P='PARKED_no_tractable_exact_mechanism_in_pass'
A={
355295:(SO,P,'Induced-saturation O(1) equivalence for all posets; infinite family, no finite certificate route identified.'),
355310:(SO,'HOLD_source_status_says_solved_body_unread','MathDB status: settled by the source paper; resolving theorem body not read in this pass; no route pursued.'),
355318:(SO,P,'Knot theory in RP^3 (class-0 non-affine genus); no Lean-feasible mechanism.'),
355353:(SO,P,'Asymptotic random-graph Builder strategy statement; no finite route.'),
355357:(SO,P,'Renyi entropy-rate continuity for all stationary ergodic processes; candidate heavy-tail renewal counterexample idea not developed; measure-theoretic Lean endpoint infeasible in pass; also existence of H_alpha is part of the ill-posedness noted by MathDB.'),
355382:(SO,P,'Foliation component classification; no route.'),
355408:('source_fetched_body_not_read',P,'Identity conjecture for generalized Eulerian triangles; recurrence/generating-function proof route plausible but not attempted.'),
355431:(SO,'HOLD_source_reports_counterexamples_body_unread','MathDB text: the source main theorem gives counterexamples of chromatic number 3 (known refutation); body not read; no credit route.'),
355543:(SO,P,'Tower-height Ramsey bound; asymptotic.'),
355590:(SO,P,'Folded ribbonlength lower bound with writhe; geometric, not attempted.'),
355613:(SO,P,'Spectral radius limits for fractal interpolation; analytic.'),
355617:('primary_statement_definitions_and_theorem_read','HOLD_literal_sign_defect_wording_correction_zero_credit','Source Theorem (Lah formula) gives chi~(X(K_3))=-1 < 0 = chi~ of a one-edge digraph; literal inequality fails trivially (n=3,4,6,8); intended |chi~| version is a corrected, non-literal question; not attempted.'),
355661:('source_fetched_body_not_read',P,'DET:IC density >= 3/4 for all cubic graphs; discharging route not attempted.'),
355689:(SO,P,'Kalai affine-stress reconstruction; geometric rigidity.'),
355701:('primary_definitions_theorem_examples_conjecture_read_arXiv_and_published','COUNTEREXAMPLE_LEAN_PASS_zero_credit_pending_root_review','9_3 configuration with maximum 4 mutually intersecting lines and no monochromatic-triangle-free line 2-coloring; refutes Conjecture 1 under inclusion-maximal and maximum readings. Lean: MathDB355701.conjectureInclusion_false, conjectureMaximum_false.'),
355740:(SO,P,'Embedded geodesic lines on complete planes; differential geometry.'),
355748:('primary_definition_theorem_conjecture_read',P,'Exact exhaustive check n<=6 confirms bound (max equals chain value); no proof; n>=7 not run.'),
355758:('source_fetched_body_not_read',P,'Locally irregular decompositions general graphs; open, no finite route beyond known verified classes.'),
355796:(SO,P,'Arithmetic fundamental lemma for Hecke functions; far beyond Lean feasibility.'),
355807:('source_fetched_body_not_read',P,'Cyclic sieving for rational Tamari rowmotion; a finite counterexample search for small coprime (a,b) is possible but not run.'),
355811:('primary_definition_and_conjecture_read',P,'Star-like defined (leaves/k-stems k<=2); mode ties make "largest index" ambiguous; exhaustive graph enumeration beyond source computations not feasible in pass without nauty.'),
355850:(SO,'HOLD_source_states_disproved_body_unread','Status: refuted in source ("Conjecture is disproved"); known; body not read.'),
355861:(SO,P,'Asymptotic edge-coloring statement.'),
355888:(SO,'HOLD_source_states_confirmed_by_Zhai_Wang_body_unread','Known resolution per source sentence; body unread.'),
355889:(SO,P,'Distinct angles Theta(n^2); asymptotic.'),
355892:('primary_definitions_theorems_conjecture_read','HOLD_literal_low_degree_failure_domain_correction_zero_credit','C_7 has semistrong index 4 > 3 = Delta^2-1 (exact), K_1 fails trivially; Delta=3 follows from source thm:cubic; real content Delta>=4 untouched.'),
355893:('primary_conjecture_and_motivation_read',P,'Subcubic <=7 except K33 and 5-prism; would need large subcubic enumeration; not run.'),
355914:('secondary_source_definition_and_conjecture_read',P,'Hartnell-Rall 2004 characterization; original 2004 body not read; no counterexample search run.'),
355946:('source_fetched_body_not_read',P,'Grothendieck leading monomials; finite computational check possible for small n but not run.'),
355956:('primary_conjecture_theorem_proof_remarks_read_arXiv_ALCO_original_followup','COUNTEREXAMPLE_LEAN_PASS_zero_credit_pending_root_review','q=5^8,d=3 gives r=1; F_5 is a clique, not maximal, in GP(5^8,3) for every field of order 5^8. Lean: MathDB355956.yip_conjecture_false and yip_conjecture_SG_false.'),
355972:(SO,P,'Convex vs Busemann functions on symmetric spaces.'),
355985:(SO,P,'Arrangement double covers torsion equivalence.'),
356036:(SO,P,'Minimal log discrepancy extremality.'),
356037:(SO,P,'Orbifold Betti/Euler extremal values.'),
356103:('source_fetched_body_not_read',P,'Zero count for evaluation codes; parameters not recovered in pass.'),
356110:('source_fetched_body_not_read',P,'Nash equilibria exact count; game definition not recovered in pass.'),
356118:(SO,'HOLD_source_states_proved_by_Ha_Nguyen_Trung_Trung_body_unread','Known resolution per source sentence; body unread.'),
356241:(SO,P,'Morse-Novikov genus.'),
356267:(SO,P,'Endoscopic character identities for covers.'),
356287:(SO,P,'Markov uniqueness conjecture (classical, famous); no route.'),
}
assert set(A)==set(res['ids']) and len(A)==40
out={}
for row in res['rows']:
    i=row['mathdb_id']; d=prov[str(i)]; r=d['record']
    pat=re.compile(r'(?<!\d)'+str(i)+r'(?!\d)'); t=row['title'].lower()
    m=[h for h in hist if pat.search(h) or t in h.lower()]
    arx=re.search(r'arxiv\.org/abs/([0-9.]+)',r.get('source_url') or '')
    arx=arx.group(1) if arx else None
    depth,outcome,assess=A[i]
    out[str(i)]={'mathdb_id':i,'title':row['title'],'literal_statement':r['statement'],
      'provenance':{k:d[k] for k in ['chunk','line_1based','chunk_sha256','raw_sha256','statement_sha256','newline_preserved']},
      'raw_file':f'raw/{i}.jsonl','source_url':r.get('source_url'),
      'outcome':outcome,'discovery_credit':0,'self_accepted':False,'new_review_depth':depth,
      'primary_receipts':[{k:x.get(k) for k in ['utc','url','status','sha256','file']} for x in receipts_for(arx)],
      'inherited_matches_count':len(m),'inherited_matches_sample':[h[:300] for h in m[:6]],
      'inherited_match_interpretation':'Bounded exact-ID/title grep (lines capped at 1200 chars) over batch history excluding mechanical corpus/screening/routing/coverage indexes and this lane; matches are administrative inventories/reservations or incidental digit substrings (byte sizes, hashes, listing rows). No unindexed old technical exclusion found. Not an exhaustive semantic audit.',
      'assessment':assess}
    if i==355956:
        out[str(i)].update({'lean':{'file':'lean/Yip355956.lean','endpoints':['MathDB355956.yip_conjecture_false','MathDB355956.yip_conjecture_SG_false','MathDB355956.not_maximal_of_card'],'axioms':['propext','Classical.choice','Quot.sound']},
          'proof':'PROOF.md §1','search_log':'logs/yip-sweep-all.jsonl','remaining':['independent statement-fidelity review (formalization of "subfield F_{p^r}" as {z | z^(p^r)=z} and of largest r via admissibleR)','independent significance/novelty review; citing literature beyond bounded search','paper']})
    if i==355701:
        out[str(i)].update({'lean':{'file':'lean/V3Config355701.lean','endpoints':['MathDB355701.conjectureInclusion_false','MathDB355701.conjectureMaximum_false'],'axioms':['propext','Classical.choice','Quot.sound']},
          'proof':'PROOF.md §2','search_log':'logs/v3-search-seed49001.jsonl','verifier':'logs/v3-verify.log','remaining':['independent fidelity review (coloring quantified over functions Finset P → Bool; triangle by source point definition)','significance review: very small counterexample to a 2023 journal conjecture','paper']})
(H/'results.json').write_text(json.dumps(out,ensure_ascii=False,indent=1)+'\n'); print(len(out))
