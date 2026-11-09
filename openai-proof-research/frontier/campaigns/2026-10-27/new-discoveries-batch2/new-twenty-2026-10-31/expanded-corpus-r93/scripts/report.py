from pathlib import Path
import json,hashlib,datetime,re
D=Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text())
def read(f):
 p=D/f
 return json.loads(p.read_text()) if p.exists() else None
notes={
'373577':('parked_no_endpoint','primary definitions and conjecture read; two independent exact small-order enumerators','Construct a shelling-degree-preserving bijection from an integral alcoved triangulation to the constrained words.',['arbor.json','arbor-6-0-108.json','arbor-7-0-40.json','arbor-7-40-80.json']),
'373586':('parked_global_closure_gap','evil-kernel definitions and source examples/proof read; truncated impartial search','Extend a kernel compatible with all sums and followers in the entire closed partizan universe, or certify a globally closed counterexample universe.',['evil.json']),
'373609':('parked_no_endpoint','exact source game definition; exhaustive, random, and twin-class minimax searches','A strategy conversion reducing palette by at most one, or an exact finite gap-at-least-two strategy certificate.',['domatic-all.json','domatic-random.json','domatic-twins.json']),
'373673':('parked_hard_general_bound','with-replacement recovery semantics and bound theorem bodies read; exact rational GF(2) diagnostics','Prove a joint mixed-column competition inequality uniformly in field, dimension and generator multiplicities.',['retrieval.json']),
'373707':('retained_historical_exclusion','history match to old routine-source-consequence exclusion; no reinvestment','Retain inherited exclusion; this lane does not adjudicate qualified historical proof claims.',[]),
'373741':('parked_no_endpoint','source reducedness/local flips and augmented connectivity proof read; independent six-tile enumeration','Simulate arbitrary droops by reducedness-preserving 2 by 2 flips, allowing nonmonotone detours, or find an exact disconnected finite instance.',['pipedream.json']),
'373768':('parked_no_endpoint','fork/perfect/good-partition definitions and source theorems read; exact graph searches','A general perfect partition meeting every maximum clique, hereditary over fork-free induced subgraphs.',['fork-all.json','fork-random.json']),
'373770':('parked_infinite_quantum_gap','primary Conjecture 1.2, Tannaka category mechanism and low-moment restrictions read','Exclude all non-easy intermediate compact quantum groups, not merely finite classical subgroups. No finite complete search of this continuous representation category is claimed.',[]),
'373809':('excluded_source_resolved_and_rank1_defect','Conjecture 1.1, Remark 1.2, Corollary 1.4 and its entire two-case proof read','None for discovery: intended r>=2 endpoint already proved in the cited source; printed r=1 fails by its own remark.',[]),
'373840':('parked_hard_planar_flow','primary planar circular-flow conjecture and surrounding 10-edge-connected scope read','Construct circular (2+1/k)-flows for all planar 4k-edge-connected multigraphs; nonplanar Jaeger counterexamples do not apply.',[]),
'373862':('parked_material_source_mismatch','live supplied abs and HTML identify a different group-theory paper; its introduction theorem bodies read','Recover the actual primary source of the quoted common-zero conjecture before mathematical investment; no access workaround attempted.',[]),
'373912':('parked_hard_classical_code_problem','source Definition 1.4, Conjecture 1.5, unrestricted counterexample and main-result scope read','Resolve commutative equivalence for all finite maximal uniquely decodable binary codes; the source weak structural form does not provide this.',[]),
'373928':('parked_no_endpoint','source colon/v/private-neighbour definitions, Theorem 3.6 proof and Theorems 4.1,4.5-4.8 read; exact GF(2) homology diagnostics','Produce an induced Stanley-Reisner restriction with homology in degree at least v-1 in the specified field, or an exact v>reg counterexample. GF(2) nonfindings do not cover every characteristic.',['graphideal-all.json','graphideal-random.json','graphideal-structured.json']),
'373963':('excluded_known_registry_subsumption','current immutable OpenAI theorem and proof assembly read; source equivalence discussion read','None for discovery: |N2|>=|N1| immediately implies each positive-epsilon version. Upstream accepted per AGENTS instructions.',[]),
'373965':('parked_no_endpoint','source Theorem 1.3 proof/classification conjecture and nonabelian critical-pair discussion read; finite connection-set searches','Analyze the nonabelian critical-pair classification including similarity and nonmaximality; finite prime-module obstruction screen is not full classification.',['cayley.json','cayley-Q16.json','cayley-F21.json','cayley-H27.json']),
'373966':('parked_no_endpoint','source Conjecture 8.1 and intended orientation context read; exact small automorphism search','Prove tightness for every distance-transitive orientation in the intended domain, especially even girth. No digon/domain correction counterexample is claimed.',['distance.json']),
'374128':('excluded_source_resolved','source Theorem 1.2, vector reduction in Section 3.1 and bipartite proof mechanism in Section 2 read','None for discovery: source already proves O(k^2) total deviation independently of t.',[]),
'374139':('parked_hard_random_matrix_asymptotic','source Conjectures 8.2 and 8.3, event comparison and model definitions read','Bound all other singular obstructions as o(P(zero column)) uniformly over 2 log n <=d<=cn, fixed c<1/2.',[]),
'374144':('parked_hard_spectral_bound','source Conjecture 7.1, dimension reduction and one-dimensional obstruction discussion read','Prove strict separation uniformly for every positive gamma in dimension one, with a complete spectral/asymptotic argument.',[]),
'374147':('parked_hard_spectral_branch_bound','source Conjecture 4.18, principal-eigenvalue proof and ball-case remark read','Control every analytic eigenvalue branch on every bounded Lipschitz domain; principal-branch and ball cases do not suffice.',[])}
out={}
for i,o in x.items():
 status,depth,gap,files=notes[i];src=o['source_url'].rsplit('/',1)[-1]
 records=[read('sources/'+src+s) for s in ['.html.receipt.json','.abs.html.receipt.json']]
 coverage={f:read('outputs/'+f) for f in files}
 if i=='373577': coverage={p.name:json.loads(p.read_text()) for p in (D/'outputs').glob('arbor*.json')}
 out[i]={**o,'outcome':status,'review_depth':depth,'credit':0,'root_acceptance':'not requested; no new endpoint','formal_endpoint_complete':False,'lean_packet':None,'source_receipts':records,'computational_coverage':coverage,'additional_coverage_files':[str(p.relative_to(D)) for p in (D/'outputs').glob('*.json') if (i in ['373609','373768','373928'] and (p.name=='atlas-search.json' or p.name.startswith('graph8-'+{'373609':'domatic','373768':'fork','373928':'ideal'}[i])))],'remaining_lemma_or_disposition':gap,'mathematical_attempts':'RESEARCH-NOTES.md','novelty_limits':'Current registry path trees screened; actual Seymour manuscript read. Source current bodies/version histories checked. No comprehensive author/citing-work search or global novelty clearance.','coverage_limits':'See RESEARCH-NOTES.md and full logs; random, truncated and GF(2) checks are diagnostics, not full-scope proofs.'}
assert len(out)==20 and set(out)=={str(i) for i in read('reservation.json')['ids']}
(D/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
# Record inherited inputs as read-only dependencies, never copy or edit shared ledgers.
paths=[D/'TASK.txt',D/'reservation.json',D.parent/'AGENTS.md',D.parent.parent/'AGENTS.md',D.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]
receipts=[]
for p in paths:
 b=p.read_bytes();receipts.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'role':'read-only instruction/context input'})
(D/'receipts/inherited-inputs.json').write_text(json.dumps(receipts,indent=2)+'\n')
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in D.rglob('*') if p.is_file() and p.name!='artifact-manifest.json' and '__pycache__' not in str(p)}
(D/'receipts/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('20 entries written; outcome counts')
from collections import Counter
print(Counter(o['outcome'] for o in out.values()))
