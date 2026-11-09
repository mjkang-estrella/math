from pathlib import Path
import json,hashlib,re,datetime
H=Path(__file__).resolve().parent
load=lambda f:json.loads((H/f).read_text()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=load('extracted.json');hist=load('history-matches.json');aliases=load('alias-matches.json')
notes={
'345741':'List-chromatic partial assignment bound: no uniform list-assignment averaging bridge proved; ordinary coloring does not suffice.',
'345757':'Foliation-depth bound requires the sutured Floer rank and taut-manifold hypotheses. No topology or Lean mechanism developed.',
'345762':'Path factor and product-balance hypotheses require primary connectedness and nontrivial-path conventions; no domain-based counterexample pursued.',
'345778':'EO-orientability order and formal-group height require primary definitions and substantial homotopy theory; no full endpoint developed.',
'345798':'Non-induced Boolean saturation comparison requires maximality for every missing subset, not a small induced-family calculation.',
'345800':'Adjoining-maximum equivalence concerns boundedness uniformly in n; no family-level transfer in both directions established.',
'345807':'Source-dependent Gamma-limit functional/cone definitions unavailable in literal record; no circular-arc variational proof attempted.',
'345822':'Cached statement explicitly reports two published dimension-four counterexamples; conservative no-investment hold, original counterexample body not reviewed here.',
'345863':'Theorem-4 function class and convolution/autocorrelation convention must be recovered before a support-endpoint argument; no wording correction pursued.',
'345866':'Lebesgue Lyapunov positivity for projective K3 dynamics is full analytic/dynamical scope; no feasible exact Lean route found.',
'345895':'Secant index requires reduced finite linear intersections; no enumerative-geometric bridge or counterexample constructed.',
'345920':'Unimodality concerns actual unlabelled benzenoid counts and convexity deficit; no enumeration semantics certified.',
'345942':'Full uniqueness/nonuniqueness phase diagram requires dimension and measure-class definitions; no statistical-mechanics proof developed.',
'345945':'Exact positive Fourier sign-uncertainty constant requires admissible function class; numerical approximation is insufficient.',
'345961':'Source threshold may be asymptotic and record has corrupted codegree notation; no tiny-n/domain correction pursued.',
'345963':'Cached record itself reports a general counterexample. No novelty claimed from an open label; original proof body unread in this lane.',
'345986':'Cached source description says the conjecture is settled. Its distance-less-than-two paraphrase is defective for a path square; no correction credit.',
'345998':'Famous 1-2-3 problem has a known-resolution lead (not body-verified in this pass); no fresh proof investment and no new exclusion theorem asserted.',
'346002':'Rainbow edge-cut colorings require simultaneous all-pairs cuts; proper edge-coloring bounds do not close the exact upper-connectivity gap.',
'346034':'Genericity and metric-graph standing assumptions omitted/corrupted; no nongeneric example can settle the generic assertion.',
'346061':'Dense Overfull Conjecture is distinct from the Core Conjecture proved in the cited source; no conflation or full proof.',
'346062':'Cached statement explicitly says equivalent reformulation is solved with the Core Conjecture; body unread, conservative no-investment hold.',
'346084':'The literal f_k definition appears inconsistent with color-isomorphic-cycle source title. Primary definition recovery required; no extremal coloring surrogate.',
'346110':'Affine-cube section extremality is full dimensional volume optimization; no exact violating subspace or sharp global argument.',
'346197':'ML degree polynomiality is an intersection-theoretic assertion with a later-resolution lead not checked here; no polynomial fit used as proof.',
'346225':'Finite-size Bethe root branch and dominant eigenvalue ordering require primary analytic definitions; no formal spectral bridge.',
'346287':'Complex-surface disjoint curves require full homology-spanning geometry; no configuration or obstruction proved.',
'346291':'Finite-field count needs maximum-scattered condition and equivalence classification, beyond counting norm values in a small field.',
'346308':'Literal calls chi_e edge-chromatic number, title/source uses perfect-matching index. No routine misdefinition counterexample pursued.',
'346330':'I_s is source-dependent and literal description as projective geometry may be wrong; no altered matroid interpretation used.',
'346388':'Full Quillen implication spans all finite groups, primes and order-complex contractibility; no low-order search can prove it.',
'346457':'Asymptotic link-graph density conjecture requires source eg definition; inherited search-only alias matches are not a prior proof or review.',
'346499':'For every fixed gonality, equality must hold for all sufficiently large genus; one explicit cover or genus sequence is not full scope.',
'346602':'Uniform oscillatory rough-integer character sum needs all q,x,y,alpha and source constant conventions; no finite experiment proves uniform cancellation.'}
primary={
'345813':(['sorting.pdf'], 'primary_definitions_and_proof_bodies_plus_sustained_attempt','parked_full_scope_collision_invariant_missing','ATTEMPTS.md#345813'),
'346099':(['gerzon.pdf','barg-musin-correct.pdf'],'primary_definitions_and_proof_bodies_plus_sustained_attempt','parked_realizability_or_inertia_bridge_missing','ATTEMPTS.md#346099'),
'346372':(['transference.pdf'],'primary_definitions_and_selected_proof_bodies_plus_sustained_attempt','parked_normalization_and_middle_index_gap','ATTEMPTS.md#346372'),
'346368':(['bicyclic.pdf','bicyclic-solved.pdf'],'primary_definitions_and_selected_proof_bodies','stop_source_correction_and_public_intended_resolution','ATTEMPTS.md#346368'),
'346096':(['borel.pdf'],'primary_definitions_and_selected_proof_bodies','parked_unrestricted_Borel_bridge_missing','ATTEMPTS.md#346096'),
'346097':(['borel.pdf'],'primary_definitions_and_selected_proof_bodies','parked_unrestricted_Borel_projection_gap','ATTEMPTS.md#346096')}
receipts=sum((load(f'fetch{n}-receipts.json') for n in ['',2,3,4]),[])
results={}
for i,e in d.items():
 r=e['record']; depth='cached_literal_statement_only';status='parked_primary_not_reviewed';files=[];attempt=None
 if i in primary:files,depth,status,attempt=primary[i]
 real=[];admin=[];numeric=[]
 for line in hist[i]['matches']:
  if not re.search(r'(?<!\d)'+i+r'(?!\d)',line) and r['title'] not in line:numeric.append(line);continue
  if '/new-twenty-2026-10-31/ledger.json:' in line:admin.append(line)
  else:real.append(line)
 results[i]={'mathdb_id':int(i),'title':r['title'],'outcome':status,'accepted_credit':0,'literal_record_read':True,'actual_review_depth':depth,'new_primary_review':bool(files),'sustained_attempt':i in ['345813','346099','346372'],'assessment':notes.get(i,'See sustained investigation in ATTEMPTS.md; no full-scope endpoint.'),'literal_statement':r['statement'],'source_url':r['source_url'],'canonical_url':r['canonical_url'],'provenance':e['provenance'],'raw_copy':f'raw/{i}.jsonl','history':{'id_title_search':'history-matches.json','source_alias_search':'alias-matches.json','technical_id_title_matches':real,'administrative_reservation_matches':admin,'numeric_substring_matches_not_reviews':len(numeric),'source_alias_matches':aliases[i]['matches'],'inherited_exact_technical_disposition_found':False,'limitation':'Bounded note/index searches; no global technical nonreview claim. Source alias 346457 matches search-result storage only, not a disposition.'},'sources_reviewed':[{'file':'sources/'+f,'sha256':sha(H/'sources'/f),'receipt':[x for x in receipts if x.get('file')=='sources/'+f]} for f in files],'attempt_file':attempt,'lean_endpoint':None,'remaining_gate':'Complete literal ordinary proof, complete semantic Lean endpoint, bounded prior-art and independent reviews; no acceptance requested.'}
assert set(results)==set(map(str,load('reservation.json')['ids'])) and len(results)==40
(H/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
# Bounded registry path screen. Truncated Omega results can establish presence only.
terms=['skew','popstack','pop-stack','gerzon','heged','packing','transference','graovac','borel','dilworth']
reg={}
for f in ['sources/current-preprints.json','sources/omega-tree.json']:
 j=load(f);reg[f]={'sha':j.get('sha'),'sha256':sha(H/f),'truncated':j.get('truncated'),'entries':len(j.get('tree',[])),'matching_paths':[x['path'] for x in j.get('tree',[]) if any(t in x['path'].lower() for t in terms)],'scope':'path screen, not body review or global absence evidence'}
(H/'registry-screen.json').write_text(json.dumps(reg,indent=2)+'\n')
print('40 results; primary-reviewed IDs:',list(primary)); print('Registry entries',[(f,j['entries'],j['truncated']) for f,j in reg.items()])
