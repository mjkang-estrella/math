"""Root documentary verification of the 336276 adversarial qualification, root exclusion record, and preparation of a second adversarial qualification of 323531; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
Q=P/'interval-kwidth-primary-qualification-sol-r2';V=P/'parking-strong-a2-source-review-sol-r1';L=P/'parking-strong-a2-primary-qualification-sol-r2';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(Q/'manifest.json');assert len(m['files'])==151==m['count'] and m['credit']==0
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=Q/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
qex=sorted(m['terminal_non_circular_exclusions']);assert set(qex)=={'manifest.json','manifest.sha256','seal_lane.receipt.json','seal_lane.output.txt'}
inventory=set()
for q in Q.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(Q)))
assert inventory==names|set(qex)
frozen(Q,43);qrec=receipts(Q,{})
ready=read(ROOT/'interval-kwidth-qualification-r2-ready.json');assert sha(Q/'TASK.txt')==ready['task_sha256']
qbudget=search(Q,2,6,2,6,['search-1-full-response.json','search-2-full-response.json']);qe=guard(Q,[Q/f'get-plan-{i}.json' for i in range(1,6)],[336276],dict(attempt=5,success=5),2)
review=read(Q/'review.json');assert set(review)=={'336276'};g=review['336276'];assert g['recommendation']=='EXCLUDE AS ROUTINE OR KNOWN' and g['branch']=='routine application only' and g['credit']==0 and g['gates']['ordinary'].startswith('PASS')
for f in ['PROOF.md','REVIEW.md','source-map.json','inventories.json']:assert (Q/f).is_file()

qs='336276 second adversarial qualification: ordinary proof and exact model PASS. ROOT SCIENTIFIC EXCLUDE AS ROUTINE, credit 0, routine branch only, and this supersedes the earlier prospective scientific pass. Actual basis, checked by root line by line: split time into m equal blocks and match the k supply copies of each block only to the demands of the next block. Each block pair is a one-dimensional nested-neighbourhood matching with exact threshold deficiency; the union of these matchings is a valid chronological matching because demand copies of a block are used only with the preceding pair and supply copies only with the following pair, losing only the first block. With the source Theorem 1 matching representation, threshold Hall and the elementary empirical-CDF law this gives limsup at most c+(1-c)/m and hence the limit, and the same proof gives the generic law for iid intervals with arbitrary continuous endpoint marginals, so the uniform case is a parameter instance of a scalar threshold formula. The all-cut suffix-maxima envelope that the first review treated as the substantive step is correct but unnecessary. Stated limits: this is a routine-application exclusion, not an authenticated earlier printed solution and not a novelty finding; Hladky-Hu-Piguet and Basdevant-Singh are recorded as theorem-level nonmatches. Strongest dissent recorded: the source and companion left the full conjecture open and a valid chronological construction is needed. Eighteen certified Lean modules are retained as uncredited research. Do not route to further formal work. 151 manifest files, 43 frozen bindings verified. Lesson recorded: a first-review creditable recommendation is not reliable until an adversarial second qualification has tried to find a generic proof.'
qr=dict(utc=now,mathdb_id=336276,source_lane=str(Q),manifest_sha256=sha(Q/'manifest.json'),verified_manifest_files=151,verified_frozen_bindings=43,verified_original_bindings=[336276],review=g,source_map=read(Q/'source-map.json'),runner_receipts=qrec,guard_events=dict(collections.Counter(e['event'] for e in qe)),search_budget=qbudget,scientific_summary=qs,reviewer_recommendation='EXCLUDE AS ROUTINE OR KNOWN',root_disposition='SCIENTIFIC_EXCLUDE_ROUTINE_APPLICATION_SUPERSEDES_PROSPECTIVE_PASS',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=qex,root_scope='Documentary integrity and root scientific disposition only; no mathematical or Lean execution by root.')
den=read(ROOT/'inherited-denials-r552.json');den['utc']=now;den['root_interval336276_qualification_r2_scope']=qs
save(P/'interval-kwidth-qualification-parent-integration-r2.json',qr);denpath=ROOT/'inherited-denials-r553.json';save(denpath,den)

for f in ['PROOF.md','REVIEW.md','review.json','source-map.json','family-comparison.json','NEW-UNAVAILABLE-REVIEW.json','search-one-response.json']:assert (V/f).is_file()
L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
for q in sorted((V/'inputs').rglob('*')):
 if q.is_file():
  d=L/'inputs'/q.relative_to(V/'inputs');d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,d)
for f in ['REVIEW.md','PROOF.md','review.json','source-map.json','family-comparison.json','NEW-UNAVAILABLE-REVIEW.json','search-one-response.json']:shutil.copyfile(V/f,L/'inputs'/('review-r1-'+f))
literal=read(L/'inputs/literal323531.json')
save(L/'reservation.json',dict(ids=[323531],rows=[literal],purpose='Second adversarial qualification of the parking-space Strong Conjecture negation; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: second adversarial qualification of MathDB 323531, the explicit A2, k=3, degree 10 equivariant hsop with 46 fixed points instead of 100, refuting the universal Strong Conjecture for parking spaces. The first review, inputs/review-r1-REVIEW.md and inputs/review-r1-PROOF.md, passed the ordinary proof and the cached literal, recommended PARK, and left the quantifier-correction objection and prior art open. In this campaign four candidates were then excluded when a deeper check found a generic route; one had even been recommended as creditable first. Your job is to try hard to do the same here, and to report honestly if you cannot.

READ FIRST. inherited-denials.json is over 270 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

PROOF. Read inputs/review-r1-PROOF.md critically and check each step. For this second review that satisfies the reconstruction requirement in the common text. Report any error, but do not re-derive what is already paid.

CLOSED WORKS, NO RECOVERY BY ANY ROUTE. arXiv 1205.4293 with its 2014 final, and arXiv 1504.06869 with its 2017 final, are closed to all new deliveries; only the supplied predelivery copies may be read. Before every GET, consider whether the host might redirect to a blocked route; a rejected redirect ends your network work, so prefer direct arXiv or open institutional PDFs you actually observed. Do not use Citeseer or Wayback.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
1. Is a non-reduced equivariant hsop a generic consequence of a parameter count? The equivariant hsops of a given degree form a parametrized family, and non-reducedness is a discriminant condition. Try to write the shortest generic proof that some hsop in the family is non-reduced, for A2 at some k and, if possible, for every rank or type: show that the discriminant is non-constant on the family and that its zero set meets the hsop locus. If this is a few lines of standard algebraic geometry, say so, because the explicit witness would then be a routine instance. If a real obstacle exists, say precisely what it is, for example why the discriminant might avoid the hsop locus, and why k=1 and k=2 behave differently. The source of the witness reports that at degree 7 a symmetric ansatz forces a common factor.
2. Was the universal quantifier understood to be an overstatement? Establish from the supplied texts what the authors said about non-generic hsops, and what the Generic Strong Conjecture was introduced to do. Decide whether a refutation of the universal form tells specialists anything they did not already expect, or whether it is a correction of the kind campaign policy gives zero credit.
3. Does later literature record this? Search for work on non-reduced parking loci, non-generic hsops, and corrections to Strong, including Armstrong-Reiner-Rhoades Parking spaces, Rhoades, Etingof, Gordon, Griffeth and later rational parking space papers, reading any applicable body through a permitted URL. Determine whether the printed Table 1 claim for A2 has a known proof or correction elsewhere.
4. Assess the Proposition 4.4 conflict. If the printed proposition is simply wrong in a way the witness exposes, say what that adds to significance. A correction of a printed error by itself earns no credit.
If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so and say what the bounded search did and did not cover. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Note that Lean modules using complex numbers, polynomial rings or ideals currently fail their kernel checks here, and say whether the literal can be stated in lighter terms such as over an explicit finite extension or by clearing denominators. The first review compared all 96 supplied scopes; spot-check that comparison rather than repeating it.

Author proposal and first review are not acceptance. Credit 0; campaign 57/60 unchanged.
'''
peers=['expanded-corpus-r524','focused-finite-routes-sol-r1'];task=common.format(lane=L,id=323531,peers=', '.join(peers))+'\nTARGET-SPECIFIC SECOND QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=323531,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'parking-qualification-r2-ready.json',rdy);save(ROOT/'selection-routing-parking-qualification-r2.json',dict(ids=[323531],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps(dict(qualification_manifest=151,frozen=43,excluded=336276,next=rdy,credit=0,accepted_new=57)))
