from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent;d=json.loads((p/'literal-record-references.json').read_text());now=datetime.datetime.now(datetime.timezone.utc).isoformat()
reasons={
339910:'As literally quantified, small x/b and unrestricted y invite endpoint failures; these would be domain corrections, not substantive sieve discoveries. No uniform sieve mechanism for intended asymptotic scope.',
339962:'Universal linear arboricity bound; no new global decomposition mechanism. Signed reformulation does not make a small known-class case eligible.',
340030:'Full Delta-equitable coloring conjecture; no concrete new coloring mechanism. Exceptions and parameter cases alone do not resolve it.',
340057:'NP-completeness requires complete reductions and a faithful complexity formalization. Record uses maximum over terminal sets, likely a fidelity issue requiring primary restoration; no shortcut credit.',
340089:'Full Hamilton-cycle/long-path alternative needs a global extremal argument; no tractable new counterexample or universal mechanism identified.',
340129:'Plane isotopy extension for arbitrary compacta needs analytic/topological machinery; no concise full construction or Lean bridge.',
340140:'Literal text is malformed and itself says conjecture finally settled. Do not promote open metadata to novelty; primary verification needed before any proof work.',
340173:'Qualitative more likely/small/large language is not an exact quantified optimization theorem. Must restore formula and tie conventions; no full theorem selected.',
340174:'Same qualitative wording issue as fixed-size companion; restoring precise service-rate formula and optimizer quantifiers is necessary before finite witness claims.',
340192:'Full additive volume extremal law; formulas alone are not a mechanism. No feasible new universal volume upper bound.',
340193:'Could enumerate finite sets, but additive dimension, affine normalization and volume bridges remain substantial; no concrete counterexample selected.',
340199:'All-dimensional exact modified zero-sum constant, including lifting and extremal lower bound. No mechanism closing arbitrary dimension/power.',
340228:'Polytope rigidity and cyclic-face hypotheses need literal primary definitions. No finite exact counterexample with every geometric bridge identified.',
340253:'Polynomial-time claim needs actual relating-edge definition and a full algorithm/correctness/runtime proof. No concrete universal algorithm selected.',
340297:'Promising six-anchor numerical asymmetric pattern, but no global symmetric lower bound, exact geometric bridge or minimizer-existence argument. See technical-notes.md.',
340327:'Requires higher-genus geometric construction and generating-series identity; no finite algebraic certificate resolves full scope.',
340364:'Extremal adjacency eigenvalue sum for arbitrary graph parameters; no new construction defeating all threshold choices e_t<t.',
340392:'Model and accuracy/optimality quantifiers not literal in record; random-graph spectral asymptotics not a feasible concise finite certificate.',
340399:'Tribonacci greedy optimality requires restoring legal moves and missing lemma label. Already-credited Zeckendorf family creates additional repeat-family risk; no primary review here.',
340408:'Uniform fractional-coloring gap below3 for all girth-five planar graphs; no mechanism for full-scope theorem.',
340423:'Universal absolute-bound equiangular configuration claim; known small dimensions are parameter instances. No new exact feasible configuration.',
340448:'Admissible cone metric definition absent from literal record; holomorphic-form dimension arguments may subsume but require actual primary work; not selected.',
340452:'All n and rank generalized EGZ exact formula; no new full zero-sum selection/lifting mechanism.',
340478:'Finite Sidon entropy claim has a complete ordinary symmetrization route, but same-object no-feedback union-channel capacity is reported known from1981. Novelty blocked; not formalized.',
340553:'All annuli Sobolev minimization needs full geometric variational proof and analytic Lean infrastructure; no concise new route.',
340561:'Source proof handles slender components, but nonassociative products outside the spine are an unresolved full-scope bridge. 2026 primary successor still asks broader question.',
340564:'NP-hardness of invariant unknotting number is not certified by diagram-crossing changes alone; no complete reduction or Lean path.',
340585:'Bijection could be finite-recursive, but modern intervals, kappa and dexter order definitions must be restored. No explicit full bijection selected.',
340615:'Uniform exponential deficit in all n,k needs extremal/topological control; endpoint examples do not earn credit.',
340617:'Full k+2 alphabet conjecture for every k and length; no constructive avoidance mechanism beyond existing Thue methods.',
340637:'Sufficiently-large-order extremal structure cannot be refuted by a lone small graph. No infinite extremal family with proof of optimality.',
340647:'Rational finite orbits tied to rational-period classification; no concrete new uniform orbit obstruction avoiding hard underlying dynamics.',
340734:'F_z is not explicitly defined in literal record. Exact shape theorem needs primary integral formula; no mechanism chosen.',
340756:'Big Heegner/Jacobi interpolation needs arithmetic-geometric infrastructure; no tractable exact universal Lean route.',
340791:'Iterated factor-degree growth dichotomy needs arbitrary-iterate estimates; small factorization diagnostics cannot close full asymptotic claim.',
340795:'Full transcendental entire escaping-set topology; no finite certificate or concise new universal construction.',
340832:'Record itself says source solves the conjecture, conflicting with open label. Requires primary verification, not rediscovery.',
340934:'Universal-vs-existential lower-bound wording conflicts with surrounding extremal discussion and older refutation references. Repeated identical permutations would be a wording shortcut, excluded.',
340936:'r-wise union condition has unspecified t and possible repeated-member/small-n conventions; exploiting literal omissions would be an endpoint correction. No genuine new full extremal bound.',
340966:'Surface-diffeomorphism construction with infinitely many ergodic MMEs requires entropy/regularity machinery; no feasible concise construction and Lean bridge.'}
res={}
for i,x in d.items():
 r=x['record'];k=int(i)
 res[i]={'mathdb_id':k,'title':r['title'],'canonical_url':r['canonical_url'],'review_depth':'literal-only','literal_statement_read':True,'primary_body_read':False,'actual_proof_read':False,'status':'PARK_NO_CONCRETE_FULL_SCOPE_ROUTE','reason':reasons[k],'accepted_credit':0,'source':{'primary_url':r['source_url'],'primary_name':r['source_name'],'primary_retrieved_this_lane':False,'corpus_file':x['file'],'corpus_line':x['line'],'corpus_record_sha256':x['record_sha256'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'corpus_retrieval_label':r.get('retrieval_source'),'corpus_lastmod':r.get('lastmod'),'review_date_utc':now},'novelty':'not established; open labels/empty solutions are not evidence','lean':{'endpoint':None,'kernel_checked':False,'axiom_audit':None,'extracted_replay':None}}
for i in ['340297','340478','340561']:
 res[i].update(review_depth='primary-and-actual-proof',primary_body_read=True,actual_proof_read=True,historical_check='r729 coverage key absent; parent and current ledgers and bounded source/ID history scan checked; see historical-scan.log and technical-notes.md',registry_check='openai/math current pinned catalogue screened; Palomar HTTP403; not novelty clearance',technical_notes='technical-notes.md')
res['340297'].update(status='PROMISING_UNPROVED_HYPOTHESIS',proof_read_scope='Bian Theorem2 reflection proof; definitions and Conjecture3. No proof of source conjecture.',diagnostics=['packing-probe.json','packing-probe.log','symmetric-dual.json','symmetric-dual.log'],next_hypothesis='For pi=(4,2,5,1,3), certify symmetric optimum>=6471/10000 and asymmetric rational packing optimum<6471/10000, then settle distinct-minimizer existence.')
res['340478'].update(status='NOVELTY_BLOCKED_KNOWN_SAME_OBJECT',proof_read_scope='Gu Prop5.9 Shannon smoothing proof; ordinary symmetrization proof derived in technical-notes. Jiang et al definitions and exact known capacity statement read;1981 original proof body not read.',ordinary_full_proof=True,independent_review=False,subsumption={'url':'https://arxiv.org/abs/1804.08599v2','scope':'same deterministic two-user union channel; sum/union bijection for finite Sidon sets','original_reported_result':'Chang-Wolf1981 DOI10.1109/TIT.1981.1056304','certainty_limit':'1981 proof body unavailable in this pass; no independent coding-theorem audit'},next_hypothesis='No discovery followup recommended; preserve as known-result exclusion, not a Lean project for credit.')
res['340561'].update(status='PARK_NONASSOCIATIVE_BRIDGE',proof_read_scope='Definitions6.1,6.5,6.7,6.10; Conjecture6.2; actual Lemma6.11/Theorem6.12/Cor6.13 proof and Theorem6.14 scope;2026 Def3.10/Problem3.11.',next_hypothesis='Construct a Monster-fusion-consistent finite non-slender component whose products interact across components, or prove all required spine complements annihilate. No bounded feasible certificate currently identified.')
(p/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
# Reference cache by path/hash; no recursive copying.
f=p.parents[1]/'lanes/sol-mathdb-primary-qualified-breadth-r482/sources/1809.01769.pdf'
# correct ancestor: fresh lane -> campaign(newtwenty) -> batch2
f=p.parents[1]/'lanes/sol-mathdb-primary-qualified-breadth-r482/sources/1809.01769.pdf'
e=json.loads((p/'source-provenance.json').read_text())
e.append({'name':'bian-existing-cache','url':'https://arxiv.org/pdf/1809.01769','version':'v1,6September2018','path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size,'retrieval_date':'historical cache; not re-fetched this lane','read_date_utc':now})
(p/'source-provenance.json').write_text(json.dumps(e,indent=2)+'\n')
(p/'progress.json').write_text(json.dumps({'date_utc':now,'reserved_ids':list(map(int,d)),'literal_read_count':40,'shortlisted_count':3,'primary_and_selected_actual_proof_count':3,'ordinary_proof_routes':1,'lean_full_proofs':0,'accepted_credit':0,'strongest_remaining_id':340297,'shared_ledger_modified':False},indent=2)+'\n')
print('wrote',len(res),'results')
