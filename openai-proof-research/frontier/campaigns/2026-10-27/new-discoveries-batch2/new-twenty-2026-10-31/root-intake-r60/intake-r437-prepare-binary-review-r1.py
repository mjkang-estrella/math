import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,base64,re,ast,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'expanded-corpus-r437';L=P/'binary-projection-ratio-source-review-sol-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
assert not L.exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'manifest.json').read_text());files=m['files']
assert len(files)==130 and all(sha(R/n)==v['sha256'] for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(n))==v for n,v in frozen.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
res=json.loads((R/'reservation.json').read_text());prov=json.loads((R/'literal-provenance.json').read_text());gates=json.loads((R/'results.json').read_text())
assert len(prov)==len(gates)==len(res['ids'])==20
assert {q['record']['mathdb_id'] for q in prov}==set(res['ids'])==set(map(int,gates))
chunks={};bindings=[]
for row in prov:
 q=Path(row['chunk'])
 if str(q) not in chunks:
  b=q.read_bytes();assert hashlib.sha256(b).hexdigest()==row['chunk_sha256'];chunks[str(q)]=b.splitlines(keepends=True)
 raw=base64.b64decode(row['raw_line_base64']);assert chunks[str(q)][row['line']-1]==raw
 assert hashlib.sha256(raw).hexdigest()==row['raw_line_sha256'] and raw.endswith(b'\n') and row['newline']
 j=json.loads(raw);assert j==row['record']
 tok=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert tok==base64.b64decode(row['statement_token_base64']) and hashlib.sha256(tok).hexdigest()==row['statement_token_sha256']
 decoded=j['statement'].encode();assert hashlib.sha256(decoded).hexdigest()==row['decoded_statement_sha256']
 assert decoded==base64.b64decode(row['decoded_statement_utf8_base64'])
 bindings.append(dict(id=j['mathdb_id'],chunk=str(q),line=row['line'],raw_sha256=row['raw_line_sha256'],token_sha256=row['statement_token_sha256'],statement_sha256=row['decoded_statement_sha256']))
receipts=[]
for n in list(files)+[x for x in m['terminal_self_exclusions'] if x.endswith('.receipt.json')]:
 if n.endswith('.receipt.json'):
  j=json.loads((R/n).read_text());receipts.append(dict(path=n,sha256=sha(R/n),exit=j['exit'],name=j.get('name'),killed=j.get('killed')))
chain=(R/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True);prev='0'*64;events=[]
for i,b in enumerate(chain):
 j=json.loads(b);assert j['seq']==i and j['previous']==prev;prev=hashlib.sha256(b).hexdigest();events.append(j)
 assert j['event'] in ['attempt','success']
 if j['event']=='success':assert sha(R/j['destination'])==j['sha256']
assert prev==m['guard_chain_terminal_sha256']
attempts=[j for j in events if j['event']=='attempt'];assert len(attempts)==10
charges=collections.Counter(str(k) for j in attempts for k in j['routes'])
assert max(charges.values())<=12
budget=json.loads((R/'search-budget.json').read_text());assert budget['actual_calls_precharged']==3 and budget['querystrings_precharged']==9
parent=P/'expanded-corpus-r437-parent-integration.json'
save(parent,dict(utc=now,source_lane=str(R),manifest_files_verified=len(files),manifest_sha256=sha(R/'manifest.json'),manifest_mismatches=[],frozen_verified=12,frozen_mismatches=[],frozen_after=after,
 raw_bindings=bindings,receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(j['exit']) for j in receipts)),GET_hops=len(attempts),GET_successes=len([j for j in events if j['event']=='success']),GET_charges=dict(charges),guard_chain_terminal_sha256=prev,new_denials=[],search_calls=3,queries=9,
 dispositions={'341052':'Ordinary investigator counterexample7/16 vs pi/2-1. Source final, probability/algorithm quantifier fidelity, Ye1999Prop1/exactNesterov2000, significant-content/wording-correction and registry proof-body obligations remain open. Send independent source/proof/significance review; no formal dispatch.','340572':'Sustained incomplete common-lower-bound weak-order fiber contractibility; source shelling does not pay interval conjecture.','340526':'Strict n3 source-conjecture correction, actual public Craig source proof read within stated partial-body limits; zero credit.','other17':'Target primary bodies explicitly unread; no scientific clearance.'},
 process_limits='Failed local dict/string persistence receipt retained, corrected SAME retained native response, no extra search. Native serialization error before shell/GET also disclosed. Sampling/native/writer limits retained.',
 root_status='INTEGRITY_VERIFIED__ONE_ORDINARY_CANDIDATE_TO_INDEPENDENT_REVIEW__NO_QUALIFIED_SURVIVOR',credit=0,accepted_new=55,target_new=60,previous_accepted=39,root_execution='Documentary integrity/orchestration only; no mathematical programs/compiler execution'))

L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]=dict(path=str(src),sha256=sha(src))
for n in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:
 cp(R/n,n)
cp(ROOT/'inherited-denials-r437.json','inherited-denials.json')
for n in ['ACTUALBRIEF.md','FULLCANDIDATE.md','DERIVATIONS.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','manifest.json','source-inventory.json','access-inventory.json','resource-inventory.json','registry-inventory.json','history-matches.json','guard-ledger.jsonl','search-budget.json','search-1-response.json','search-2-response.json','search-3-response.json','get-binary-plan.json','get-binary-record-plan.json','get-nesterov-plan.json']:
 cp(R/n,'inputs/author/'+n)
for n in ['binary.pdf','binary.txt','binary-record.html','nesterov.pdf','nesterov.txt','registry-openai.html','registry-leanpool.html','registry-tau.html','registry-google.html']:
 cp(R/'sources'/n,'inputs/sources/'+n)
targetrow=next(q for q in prov if q['record']['mathdb_id']==341052)
(L/'inputs/literal341052.jsonl').write_bytes(base64.b64decode(targetrow['raw_line_base64']))
save(L/'inputs/341052-gates.json',gates['341052'])
cp(ROOT/'accepted55-path-review-context.json','inputs/accepted55-routing.json')
cp(P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json','inputs/prior39-routing.json')
cp(parent,'inputs/ROOT-AUTHOR-INTEGRATION.json')
save(L/'INPUT-ORIGINS.json',origins)
save(L/'reservation.json',dict(ids=[341052],mathdb_id=341052,source_url='https://arxiv.org/abs/1811.05873',author_lane=str(R),role='Independent full proof, source probability/algorithm semantics and prior/significance qualification',credit=0,accepted_new=55,target_new=60))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n')
save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Inherited denial union r432','Inherited denial union r437')
detail='''Independent full ordinary/source/prior/significance qualification of MathDB341052, Mo-Duarte Binary sequence design arxiv1811.05873v1 Conjecture1. This is NOT formal execution. Protected active/planned peers: shoe-pair-discrepancy-formal-sol-r4 and cmdrr-five-three-formal-independent-review-sol-r5. Never access their metadata/bodies. All input copies frozen; cannot edit author evidence. Source downloads and current record/NesterovCORE9860 already cached, no refetch. Read literal341052, FULLCANDIDATE, source full sections3.2/4.1-4.3/equations24-25/Algorithm1/Conj1 and exact references, including source appendices relevant to expectation vs deterministic guarantees. Independently verify every hypothesis and quantify precisely over optimal SDP solution, random realization, finite search/tie-breaking/selected feasible output and tolerances. Pay original source and literal statement separately, no declared interpretation waiver.

Proposed witness N8, alpha5, DC-only interferer and complementary seven normalized Fourier columns message, S=(8/7)(I-J/8) is optimal SDP objective8, rounded sevenplus/oneminus feasible original interference9/2<5 with message7/2 ratio7/16<pi/2-1. Check disjoint/nonempty band and any implicit contiguous-band/source admissibility restriction, normalized DFT complex-to-real PSD/correlation assumptions, alpha/2 SDP constraint, true global optimality not arbitrary matrix, singular Gaussian support, strict nonzero signs and positive probability, arbitrary eigendecomposition/eigenvalue multiplicity, exact finite-searchselection L1 or all L fixed. No Python numerical/enumerative check. Supply full independent ordinary proof or exact gap and repair if valid, including all finite-dimensional and probability bridges needed for a future literal Lean theorem. Do not replace an actual randomized-support endpoint with a bare binary feasible-vector instance.

PRIMARY comparison obligations identified by author: Ye1999 Proposition1, exact2000 Nesterov chapter source ref40 (cached CORE1998 report is NOT authenticated text-identical), source ref29 Nesterov1998. Identify actual bibliographic titles/versions from references; inspect actual theorem+proof where needed within targeted8GET-hop total/perID and2search/6query budget. No guessed alternate routes/seed lists/whole-work retries after failure. Source journal/final/correction publication identity/current version also requires targeted bounded assessment; onlyv1 record/nojournalref is not global nofinal evidence. Current4registry roots cached, avoid refetch; exact matching proof body only if actual candidate found. Inherited latest denial union binds all failed older works, no exception here. Distinct prior work may be newly fetched if not denied; cannot indirectly deliver denied work. Each persisted manually selected guard plan routes341052, budget8 actual hops not merely8 helper calls. Search snippets navigation only, actual body before reliance, stop affected route on failure without alternate delivery or retries.

Crucial significance/qualification question: is this a substantive new exact refutation, a routine adaptation of an applicable earlier theorem/counterexample, or merely an expectation-versus-pointwise/algorithm-output quantifier correction of the intended conjecture? Give strongest arguments BOTH ways. No automatic exclusion based on simple covariance/standard rounding/shortness, nor automatic credit because source says conjecture. For exclusion document a COMPLETE prior-result-to-this-endpoint bridge or exact intended/literal correction; distinguish an analogous expected approximation theorem (existence or max-minus-min normalized guarantee) from every feasible draw with off-diagonal Fourier constraint. Even a technical PASS leaves root adjudication. Specific unread applicable prior body is HOLD; bounded worldwide nonmatch alone not automatic veto. Compare94 trusted accepted scopes only, no prior certificate audits.

Preserve author limits: source relevant definition/body passages read, empirical plots not used, exact2000chapter/YeProp1 unread, native search dict/string serialization repair same retained response, other17 primary bodies unread do not imply anything about this candidate. Fresh review cannot repair author logs/ledger. Report own process/access failures candidly. If primary/source semantics fail, still close independent math/source analysis without numerical evidence. Deliver REVIEW.md, full INDEPENDENT-PROOF.md or GAP.md, keyed review.json separate literal/original/final/math/probability/prior/novelty/significance/family/process/formal/acceptance gates, exact objections/contrary arguments and dependency-ordered DORMANT obligations if suitable. No Lean/formal dispatch or acceptance/credit. Current55/60 beyond39 remains unchanged. Preserve every completed receipt incl failed outcomes, plans/hashchain/source/search data, final standalone frozenafter and manifest exact terminal exclusions.
'''
task=('Independent focused review341052 in '+str(L)+'\n'+common.replace('LANE',str(L)).replace('TARGET','341052')+'\nSPECIFIC SCOPE:\n'+detail)
(L/'TASK.txt').write_text(task)
ownfiles=[q for q in L.rglob('*') if q.is_file() and q.name!='search-budget.json']
bind={str(R/n):v['sha256'] for n,v in files.items()}
bind[str(R/'manifest.json')]=sha(R/'manifest.json')
for n in m['terminal_self_exclusions']:bind[str(R/n)]=sha(R/n)
bind.update({str(q):sha(q) for q in ownfiles})
save(L/'frozen-inputs.json',bind)
save(L/'ROOT-PREP.json',dict(utc=now,lane=str(L),target=341052,model='gpt-6.1-sol',reasoning='high',service='default',frozen_count=len(bind),reservation_sha256=sha(L/'reservation.json'),task_sha256=sha(L/'TASK.txt'),credit=0,campaign=55,budget=dict(GET_hops=8,search_calls=2,queries=6),protected_peers=['shoe-pair-discrepancy-formal-sol-r4','cmdrr-five-three-formal-independent-review-sol-r5']))
assert all(sha(Path(n))==v for n,v in bind.items())
save(ROOT/'binary-review-r1-ready.json',dict(utc=now,lane=str(L),target=341052,frozen=len(bind),task_sha256=sha(L/'TASK.txt'),author_manifest_count=len(files),author_verified_bindings=len(prov),credit=0))
print(json.dumps(dict(parent=str(parent),author_files=len(files),author_frozen=len(frozen),raw_bindings=len(bindings),receipts=len(receipts),exits=dict(collections.Counter(str(j['exit']) for j in receipts)),review_lane=str(L),review_frozen=len(bind))))
