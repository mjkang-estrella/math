from pathlib import Path
import json,hashlib,datetime,re,zipfile
O=Path(__file__).resolve().parent;r=json.loads((O/'reservation.json').read_text());rec=json.loads((O/'records.json').read_text());prov=json.loads((O/'provenance.json').read_text());hist=json.loads((O/'history-screen.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
notes={
363326:'Literal omits the difference and small-parts conditions defining B; recover exact source conditions before any generating-function mechanism.',
363327:'Requires an infinite family with exponential eventual outcome period in maximum subtraction; finite long-period searches would not prove this existential asymptotic claim.',
363337:'Need primary LSS ring definition, base field and forest hypotheses; an isolated/edgeless special case risks source-scope correction. No class-group proof attempted.',
363363:'Full dimension-uniform KLS inequality; no feasible unrestricted Lean mechanism identified from literal review.',
363375:'Need local-field hypotheses and full odd-isogeny valuation mechanism; modular-polynomial sample checks would not prove universal statement.',
363379:'Literal calls Snort impartial; source game definitions and thermographic temperature must govern. No correction-based candidate selected.',
363401:'Must recover scattered-subword occurrence multiplicities; contiguous-substring monotonicity is not a valid bridge.',
363407:'Empirical parameter-selection language lacks quantified objective/distribution/comparison; no literal exact theorem selected.',
363417:'Need all signed-sum radius and abelian-group semantics and sharp existence for each s; no finite-order instance would resolve full formula.',
363428:'Corrupted degree inequalities require primary recovery; no claim from a reversed inequality or fixed number of colors.',
363432:'Need torsion PDE, boundary regularity and fail-point interpretation; no symmetric smooth counterexample or full comparison derived.',
363434:'Need full arboricity decomposition mechanism for all d,k; old title match is abstract catalogue only, not a prior exclusion.',
363489:'Need torus plaid, t(n), a,b and optimization quantifiers from primary; no surrogate queen-array objective attempted.',
363522:'Corrupted notation and correspondence hypotheses require primary scope; no manageable full local-Langlands formalization route.',
363548:'Need source tiling regularity and maximum/supremum interpretation; no degenerate-tile correction candidate selected.',
363584:'Literal leaves Delta(delta) undefined; no feasible guarantee can be proved before primary Slater-bound recovery.',
363606:'Exact sequence iteration potentially admits finite obstructions, but source normalization and strictness must be recovered before a certified coefficient sweep.',
363613:'Literal explicitly says Joos-Kim confirmed it; primary proof body not read here, so retained as prior-resolution lead rather than new verified exclusion.',
363683:'Need original k range and min-degree hypotheses; negative k literal loophole would be a scope correction, not a qualifying target.',
363691:'General cycles-plus-K4 coloring problem; source only records a conditional reduction; no full constructive coloring algorithm derived.',
363698:'Need exact temperate definition and full even-dimensional extremal family; no missing-small-k endpoint refutation attempted.',
363749:'Source sheaf/wall/F-admissibility definitions absent from literal; no exact general syzygy statement reconstructed.',
363759:'Full source scope recovered; partition-histogram derivation and 800 order-9 graph sample, no nonisomorphic collision. Need full-B collision or general coefficient reconstruction.',
363785:'Source title announces a Pach-Tardos refutation and literal identifies r=2 equivalence. Material prior-resolution lead; body unread, no new theorem or verified exclusion asserted.',
363816:'Need full partition placement of benchmark K_Delta,Delta copies; optimizing an arbitrary placement would change the question.',
363827:'Need exact moving-target coprimality and limsup sets; preceding strong-version counterexample does not settle this weak version.',
363831:'Need exact oriented-graph convention and dichromatic bound; no general coloring mechanism. Small local examples alone would require source-faithful certificates.',
363857:'Historical dilogarithm identity presented in a modern monograph; inspect exact primary theorem/proof before treating its conjecture label as live. No known-result formalization attempted.',
363861:'Need a full quasirandom-forcing certificate with fewer than eight permutations or a universal lower bound, rather than finite sampled permutons.',
363921:'Corrupted matroid notation and asymmetric maximum require original conjecture recovery; no wording-based counterexample.',
363954:'Need source asymptotic quantifiers in n and lift size and probabilistic Hajós bounds; no finite lift diagnosis resolves them.',
363966:'Primary isoperimetric-constant definition and source resolution status required; no finite Markov-chain constant-factor violation suffices without an unbounded family.',
364019:'Missing gamma range, Euler products, GRH/family hypotheses and asymptotic quantifiers require source recovery; no pole-range loophole.',
364026:'Need delta-tameness and allowed base measures including tail/moment hypotheses before a heavy-tail counterexample can qualify.',
364027:'Undefined Theorem(ii) requires exact ESD conclusion and conditioning regime; no changed limiting law or moment hypothesis assumed.',
364087:'Primary and published definitions recovered; binomial lifting and support-transfer attempts leave a spread-preserving realization lemma open.',
364095:'Kernel-proved K5 obstruction to four set palettes, exact source universal-minimum negation; fresh strict replay and all-local audit pass. Independent source, novelty and significance review required.',
364097:'Literal itself asserts falsity using a related Hurwitz-order objection; need actual source uniqueness statement and valid implication, not that adjacent assertion alone.',
364099:'Need source Clifford-Euclidean division and bubble/fundamental-domain equivalence; no geometric certificate produced.',
364118:'Published primary definitions and proofs read; refined-count binomial inversion does not invert unrestricted Cayley counts. Finite insertion-length checks do not prove all-pattern maximum recovery.'}
source_map={363759:['signed'],364087:['spread','spread-published'],364095:['palette','palette-abs','palette-author'],364118:['cayley']}
results={}
for i in r['ids']:
 k=str(i);x=rec[k];selected=i in source_map
 sources=[]
 for name in source_map.get(i,[]):
  receipt=json.loads((O/'sources'/f'{name}.receipt.json').read_text());sources.append({'name':name,'receipt':f'sources/{name}.receipt.json',**receipt,'text_sha256':sha(O/'sources'/f'{name}.txt') if (O/'sources'/f'{name}.txt').exists() else None})
 outcome='hold_statement_only_no_primary_clearance'
 if i==364095:outcome='formal_refutation_candidate_pending_independent_review'
 elif selected:outcome='sustained_route_parked_unresolved'
 elif i in [363613,363785,363857,364097]:outcome='hold_material_prior_or_source_status_lead_body_unread'
 results[k]={'mathdb_id':i,'title':x['title'],'canonical_url':x['canonical_url'],'outcome':outcome,'accepted_credit':0,'literal_statement':x['statement'],'literal_provenance':{'raw_file':f'raw/{i}.jsonl',**prov[k]},'source_url':x['source_url'],'source_name':x['source_name'],'inherited_matches':hist[k],'inherited_target_exclusion_found':False,'new_review_depth':{'literal_read':True,'primary_definitions_read':selected,'primary_proof_passages_read':i in [363759,364095,364118],'whole_primary_paper_read':i==364095,'review_detail':'ATTEMPTS.md' if selected else 'Literal statement only; no source-body exclusion or novelty assertion.'},'new_source_receipts':sources,'mathematical_attempt_or_remaining_gap':notes[i],'lean_endpoint':'Palette.source_refutation : ¬ Palette.SourceClaim' if i==364095 else None,'novelty_clearance':False,'limitations':'No all-corpus technical review, worldwide priority clearance or current MathDB/Palomar clearance. Open metadata labels are not evidence of novelty.'}
assert len(results)==40 and set(map(int,results))==set(r['ids']);(O/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
inputs=[]
for p,h in r['input_hashes'].items():
 actual=sha(Path(p));inputs.append({'path':p,'reserved_sha256':h,'actual_sha256':actual,'matches':actual==h})
(O/'input-verification.json').write_text(json.dumps({'inputs':inputs,'campaign_ledger_is_mutable_context':True,'reservation_sha256':sha(O/'reservation.json')},indent=2)+'\n')
log=(O/'fresh-Audit.log').read_text();count=re.search(r'LOCAL_TOTAL (\d+)',log).group(1);axs=re.findall(r'TRANSITIVE_AXIOMS (.*?) \[(.*?)\]',log);assert len(axs)==int(count);assert all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for _,a in axs);assert not any(x in log for x in ['sorryAx','native_decide','ofReduceBool']);(O/'audit-summary.json').write_text(json.dumps({'all_local_declarations_including_generated':int(count),'module_origins':['Defs','BoolProbe','Checker','Endpoint'],'audit_module_excluded_from_mathematical_inventory':True,'all_isUnsafe_false':True,'new_axioms':0,'allowed_transitive_axioms':['propext','Classical.choice','Quot.sound'],'all_transitive_print_axioms_passed':True,'audit_log_sha256':sha(O/'fresh-Audit.log'),'kernel_decide_only':True},indent=2)+'\n')
files=['Defs.lean','BoolProbe.lean','Checker.lean','Endpoint.lean','Audit.lean','environment.json','guard.py','replay.py','audit-summary.json','replay-result.json','ATTEMPTS.md','palette-independent.log','palette_independent.py','fresh-Audit.log','sources/palette.bin','sources/palette.receipt.json']
with zipfile.ZipFile(O/'364095-proof-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files:z.write(O/f,f)
(O/'proof-packet-manifest.json').write_text(json.dumps({'packet_sha256':sha(O/'364095-proof-packet.zip'),'files':{f:sha(O/f) for f in files},'requires_external_pinned_upstream_cache':True},indent=2)+'\n')
print('40 results; audit declarations',count,'packet',sha(O/'364095-proof-packet.zip'))
