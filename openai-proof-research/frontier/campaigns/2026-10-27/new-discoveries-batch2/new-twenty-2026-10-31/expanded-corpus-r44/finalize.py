import json,hashlib,resource,os,datetime
from pathlib import Path
P=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
h=lambda b:hashlib.sha256(b).hexdigest(); prov=json.loads((P/'literal-provenance.json').read_text()); reservation=json.loads((P/'reservation.json').read_text());receipts=json.loads((P/'source-receipts.json').read_text());hist=json.loads((P/'history-id-matches.json').read_text())
primary={350817:('2105.13357','conditional_source_context','Conjecture6.3; conditional Lemmas6.4–6.6 proof bodies; full Gaussian toric semantics unreviewed'),350818:('2105.13357','conditional_source_context','Conjecture6.7; conditional lemmas read; safe-gluing definitions and complete classification unaudited'),351026:('2106.09209','primary_and_successor_proof','Original Conjecture5.1 and definitions; successor2512.22761 Theorem3.1 full induction/Corollary3.2 proof'),351027:('2106.09238','sustained_primary_proof_attempt','Actual matrix/graph definitions; Lemma5.2 and Theorem5.1 proof, Theorem5.3 comparison at alpha=1/2; all-alpha gap remains'),351252:('2107.04998','full_short_primary_refutation_body','Entire note including matching/ex/chromatic definitions and snark refutation'),351300:('2107.07368','sustained_primary_proof_attempt','Full rules and Upsilon definition, Observation9/Theorems10–12 proofs/Conjecture20; belief-state diagnostic'),351322:('2107.09025','primary_and_successor_proof','Original definitions and Conjecture3.4; institutional successor Theorem1.1 and concluding proof; auxiliary cases not all audited; publisher version not body-read'),351537:('2108.02363','primary_statement_fidelity_check','Source Conjecture1 and conclusion; raw iff does not match; no attempted raw-paraphrase refutation'),351574:('2108.03943','primary_definitions_and_bounds_proof','Imprimitive action definition, Lemma4.1 proof, Proposition4.4 proof and Conjecture4.6; product-action wording mismatch'),351662:('2108.08118','primary_prior_refutation_report_only','Source Conjecture1 and introduction report; original counterexample construction bodies unread; old r285 exclusion retained'),351663:('2108.08118','sustained_primary_proof_attempt','Conjecture3, Theorem4 statement and entire Theorem5 proof; structural and matching attempts'),351664:('2108.08118','primary_and_successor_main_proof','Source Conjecture9; Pinter2607.06515 Theorem1.1, boundary-state/induction context and full Section5 proof; finite certificate not independently replayed')}
reasons={
350817:'HOLD: Gaussian polynomial-ideal and d-separation semantics still need complete source recovery; no proof/counterexample. Endpoint/nonexistent-separator ambiguities are not eligible.',
350818:'HOLD: conditional conjecture and safe-gluing semantics not fully recovered. No credit from complete-DAG or decomposition degeneracies.',
350875:'HOLD literal only: finite-field clique characterization; later partial/full-resolution leads not body-audited. No Peisert search or clearance claimed.',
351014:'HOLD literal only: broad C^r symplectic closing statement, outside a tractable new full-scope Lean mechanism in this pass.',
351021:'HOLD literal only: pendant-path independent-set EKR range requires primary definitions and current resolution check before testing.',
351026:'EXCLUDE_PRIOR_PROOF: Liu–Diwan–Zhang2512.22761 Theorem3.1/Corollary3.2 prove exact bound; actual induction and substitution read.',
351027:'HOLD_STRONG_ROUTE: all-length Schur reduction, exact symbolic determinant identities, finite numerical diagnostics; universal sign lemma and parameter-domain/Lean bridges unproved.',
351105:'HOLD literal only: graph family and maximal spectral gap semantics require actual primary definition; no endpoint correction claimed.',
351138:'HOLD literal only: rank-four Steenrod quotient/GL4 invariant kernel requires full primary algebra semantics; no finite-dimensional surrogate theorem.',
351161:'HOLD literal only: kinetic equilibria and dynamical stability not defined fully in record; all-dimension proof absent.',
351186:'HOLD literal only: degenerate-graph flap exponent and current successor literature not body-audited; no universal asymptotic result asserted.',
351187:'HOLD literal only: primary-search lead reports a Huynh–Wood conjecture refutation with torso conditions, but no exact primary bridge/body read; do not declare this ID resolved.',
351189:'HOLD literal only: record reference reports a refutation of related dispersability conjectures, without this pass reading exact construction/scope. No blanket exclusion from metadata.',
351234:'HOLD literal only: admissible minimization class absent in raw record; no mathematical endpoint selected from an informal physical principle.',
351252:'EXCLUDE_PRIOR_REFUTATION: selected source itself proves snark matching-Kneser chi=1 versus RHS3. Full short note read.',
351266:'HOLD literal only: asymptotic Brownian estimator/time-scale semantics require source recovery; no bounded diagnostic substituted.',
351295:'HOLD literal only: asymptotic permutation-square covering claim; no source-proof audit or all-n mechanism.',
351300:'HOLD_STRATEGY_GAP: source minimum-Upsilon definition recovered; mixed factor strategy invariant missing. Finite solver covers31 small factors, all already in source-bound regime.',
351322:'EXCLUDE_PRIOR_PROOF: institutional Bora–Choi–Tang Theorem1.1 supplies exact path-spum formula; concluding proof read. Published version identified, not independently body-audited.',
351368:'HOLD literal only: Coxeter gate/Garside-shadow definitions and later resolutions need primary comparison. No credited Coxeter-family variant attempted.',
351380:'HOLD literal only: triangular-pyramid graph definition and full-n extremal bound require primary recovery; no small-n endpoint correction.',
351396:'HOLD literal only: projective-space linear-code operations/metric semantics need primary recovery; no routine dimension surrogate.',
351406:'HOLD literal only: instanton Floer differential construction and projective scalar equality require source body; no formal endpoint.',
351423:'HOLD literal only: dilation-surface/geodesic scope requires primary and current resolution audit; no ordinary proof.',
351491:'HOLD literal only: sufficiently-large-n planar induced-cycle optimum not reduced to small finite search.',
351500:'HOLD literal only: sufficiently-large odd-cycle threshold multiplicity, no all-length proof mechanism recovered.',
351501:'HOLD literal only: exact threshold Ramsey number and path-copy conventions need source recovery; no new proof.',
351524:'HOLD literal only: rigidity/weak ML threshold semantic bridge and cycle-converse current status unaudited; no endpoint.',
351537:'STOP_SOURCE_FIDELITY: source does not state raw iff. Attacking nonplanar or high-degree necessity would address defective paraphrase, not eligible discovery.',
351540:'HOLD literal only: metadata solved quote may address a different cycle subcase; exact degree-two rainbow theorem bodies unread.',
351541:'HOLD literal only: t=2n+1 quote does not by itself settle all t>=2n+1; actual primary proof unread.',
351563:'HOLD literal only: exact Core Conjecture and later full/partial theorem bodies unreviewed; no graph sweep or open-status certification.',
351574:'HOLD_ACTION_FIDELITY: source action is on V times N (imprimitive), unlike raw product-action label; source bounds do not prove equality. No change-of-action credit.',
351599:'HOLD literal only: reduced Bernstein–Sato/singularity-level definitions, floor convention and current theorem scope not audited.',
351620:'HOLD literal only: source subcubic/girth and degree-two boundary conventions need primary comparison; no endpoint correction credit.',
351637:'HOLD literal only: Harborth matchstick exact bound; retrieved search lead offers only an improved bound, not a full theorem-body resolution.',
351643:'HOLD literal only: source solved quote not proof of sufficiently-large-l uniqueness; primary extremal-family definitions unread.',
351662:'EXCLUDE_INHERITED_ORIGINAL_REFUTED_FAMILY: old r285 scout exclusion and actual source report retained; counterexample bodies unread here; no new refutation attempted.',
351663:'HOLD_STRONG_ROUTE: exact induced-star-forest reformulation and matching/max-cut repair attempts;150 finite bipartite samples colorable; no universal repair lemma or Lean.',
351664:'EXCLUDE_PUBLIC_FULL_SCOPE_PROOF: Pinter2607.06515 Theorem1.1 and main proof read; finite certificate and full grammar not independently replayed.'}
result={}
for i in reservation['ids']:
 v=prov[str(i)];record=v['record'];d=primary.get(i);src=[]
 if d:
  names=[d[0]+'.pdf']
  if i==351026:names+=['2512.22761.pdf']
  if i==351322:names+=['bora-choi-tang.pdf']
  if i==351664:names+=['2607.06515.pdf']
  src=[r for r in receipts if Path(r.get('file','')).name in names]
 old=[]
 if i in [351662,351663,351664]:old=[{'path':str((P.parent.parent/'lanes/sol-primary-diverse-certifiable-scout-r285/SCOUTING.md').resolve()),'relationship':'Section1 excludes original refuted cubic family and vague relaxations; exact bipartite and outerplanar subclasses are not thereby excluded','sha256':h((P.parent.parent/'lanes/sol-primary-diverse-certifiable-scout-r285/SCOUTING.md').read_bytes())}]
 result[str(i)]={'mathdb_id':i,'title':record['title'],'canonical_url':record['canonical_url'],'literal_statement':record['statement'],'literal_source_url':record['source_url'],'provenance':{k:x for k,x in v.items() if k!='record'},'raw_file':f'raw/{i}.jsonl','inherited_matches':old,'history_id_hits':hist[str(i)],'history_title_exact_hits':[],'history_limit':'Exact numeric boundary search and exact titles over campaign markdown/results/ledgers; no exact prior technical ID entry found beyond assignment ledger. Related-family leads separately retained; not global nonreview.','review_depth':{'literal_read':True,'primary_read':bool(d),'level':d[1] if d else 'literal_only_primary_unread','new_primary_detail':d[2] if d else 'No primary definitions, theorem statements or proof bodies read for this ID in r44.','inherited_vs_new':'Raw corpus metadata is inherited; cited primary review is new in this pass. Prior counterexample construction for351662 remains unread.'},'outcome':reasons[i].split(':')[0],'reason':reasons[i],'attempts_reference':'ATTEMPTS.md' if d else None,'source_receipts':src,'registry_limit':'See registry-screen.json: bounded current path screen only, not proof-body clearance. MathDB/Palomar inherited403 not clearance.','ordinary_full_proof':False,'lean_literal_endpoint':None,'new_credit':0,'root_acceptance_required':True}
assert len(result)==40 and set(map(int,result))==set(reservation['ids']);(P/'results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
# Verify every manifest-bound chunk, newline-preserved extraction and reservation input hashes.
C=P.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';manifest=json.loads((C/'manifest.json').read_text());chunks=[x for x in manifest['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20
validation={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'chunks':[],'raw_ids':[],'input_hashes':[]}
for x in chunks:
 actual=h((C/x['path']).read_bytes());assert actual==x['sha256'];validation['chunks'].append({'path':x['path'],'sha256':actual,'manifest_match':True})
for i,v in prov.items():
 raw=(P/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and h(raw)==v['raw_sha256'];line=Path(v['chunk']).read_bytes().splitlines(keepends=True)[v['line_1based']-1];assert line==raw;assert h(json.loads(raw)['statement'].encode())==v['statement_sha256'];validation['raw_ids'].append(int(i))
for f,want in reservation['input_hashes'].items():
 actual=h(Path(f).read_bytes());validation['input_hashes'].append({'path':f,'sha256':actual,'reservation_match':actual==want,'mutable_ledger':f.endswith('/ledger.json')})
validation['result_count']=len(result);validation['primary_context_ids']=list(primary);validation['literal_only_count']=40-len(primary);validation['no_lean_endpoint']=True
(P/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
formal=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');lm=json.loads((formal/'lake-manifest.json').read_text());env={'lean_binary':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','lean_version':(P/'lean-version.log').read_text().strip(),'manifest_path':str(formal/'lake-manifest.json'),'manifest_sha256':h((formal/'lake-manifest.json').read_bytes()),'packages':lm['packages'],'dependencies_read_only':True,'certificate_status':'No theorem written; no strict extracted build or axiom audit claimed.','cache_trust_limit':'Prebuilt dependency oleans are external trusted cache; no complete upstream source rebuild or attestation performed.','resource_caps':'Mathematical scripts set affinity<=2 CPUs,6GiB AS,90–150 CPU seconds and105–170s external wall timeout. Lean version probe8GiB AS/20 CPU seconds/25 wall seconds. Fetch scripts6GiB AS and<=2 workers.','initial_diagnostic_failure':'First diagnostics run lacked networkx; retained in work log description, replaced with dependency-free graph implementation. Final diagnostic script uses NumPy and SymPy only where stated.'}
(P/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
print('validated',len(result),'IDs;',len(primary),'primary contexts;',len(chunks),'manifest chunks; zero credit')
