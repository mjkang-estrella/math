"""Root documentary verification of r519 and preparation of an independent 362896 review; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r519';L=P/'simplex-three-design-source-review-sol-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
aex=manifest(A,'manifest.json',209,'seal_manifest','terminal_noncircular_self_exclusions');frozen(A,13);arec=receipts(A,{})
aman=read(A/'manifest.json');assert aman['credit']==0 and aman['qualified_survivors']==0 and aman['author_full_ordinary_proposals']==[362896]
route=read(ROOT/'selection-routing-r519.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'corpus-bindings.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in prov}
sources={};bound={}
for v in prov:
 raw,obj,token=corpus(v);key=str(obj['mathdb_id']);assert key==str(v['id']) and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['statement'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'];sources[key]=obj['source_url'];bound[key]=(raw,obj,v)
assert collections.Counter(v['disposition'] for v in gates.values())=={'PARK_PRECISE_GAP':18,'EXCLUDE_EXACT_PUBLIC_RESULT':1,'HOLD_FULL_AUTHOR_ORDINARY_PROPOSAL':1} and all(str(v['credit'])=='0' and not v['qualified_survivor'] for v in gates.values())
assert gates['362896']['disposition']=='HOLD_FULL_AUTHOR_ORDINARY_PROPOSAL' and gates['328631']['disposition']=='EXCLUDE_EXACT_PUBLIC_RESULT'
abudget=search(A,3,9,3,9,['search-response-1.txt','search-response-2.txt','search-response-3.txt'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=11,success=8,redirect=3),5)
fr_at=[e for e in ae if e['event']=='attempt' and ('0277112' in e['url'])];assert len(fr_at)==3 and (A/'NETWORK-STOP.md').is_file()
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');names={x['path'] for x in hist};assert len(hist)==896 and len(allow)==898 and names<=set(allow) and len(set(allow)-names)==2
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and 'interval-kwidth' not in x['path']
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r519 zero qualified survivors, one author-complete ordinary proposal, independently unreviewed. 362896: no equal-weight d-point simplex 3-design for any d>=3, source Conjecture 7 of Gonzalez Avella, Czartowski, Goyeneche and Zyczkowski, Quantum 9, 1763 (2025). Mechanism: the second-moment conditions force a regular-simplex Gram matrix by a finite sum of squares; the cubic moment array of any such point set then has squared norm (d-1)(d-2)/(d^3(d+1)^3), while the uniform simplex has 4(d-1)(d-2)/(d^3(d+1)^2(d+2)^2), and equality forces d^2=0. Independent proof, prior, novelty, significance, family, formal, paper and acceptance gates unpaid. Specific prior HOLD: Fritsch 1970 on minimal third-degree integration formulas returned a challenge-bearing page, is closed and unread; predecessor 1308.3188 unread; classical Gaussian cubature may subsume this. 328631 is an exact public refutation in 2504.11656, zero. 358105 has three sustained routes and an unpaid gadget lemma. Eighteen assigned original bodies unread; recorded gaps are not open-status certifications. Verified 209 manifest files, 20 corpus bindings, 13 frozen, 896 saved history entries, 11 charged GET hops (8 transport successes including 5 PDF, 3 redirects), 3 searches / 9 strings with responses saved. No formal dispatch or credit.'
work='F. N. Fritsch, On the existence of regions with minimal third degree integration formulas, Math. Comp. 24 (1970) 855-861, DOI 10.1090/S0025-5718-1970-0277112-8, JSTOR 2004619'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/author/cache/mirror/DOI/API/indirect deliveries unavailable after the DOI chain returned HTML with a challenge-platform marker; no script, retry or alternate recovery. Its actual theorem and proof remain unread. Distinct cubature works are not blanket denied.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),task_reservation_genesis_verified=True,verified_manifest_files=209,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),verified_saved_history_names=896,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_ONE_AUTHOR_PROPOSAL_ROUTED_TO_INDEPENDENT_REVIEW',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r540.json');den['utc']=now;den['root_r519_scope']=ass;den['root_simplex362896_fritsch_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{e['url_key'] for e in fr_at});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'10.1090/s0025-5718-1970-0277112-8'})
den['records'].append(dict(url=fr_at[0]['url'],reason=dict(status=200,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r519-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r541.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:shutil.copyfile(A/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
raw,literal,binding=bound['362896'];(L/'inputs/original362896.raw.jsonl').write_bytes(raw);save(L/'inputs/literal362896.json',literal);save(L/'inputs/provenance362896.json',binding);save(L/'inputs/author-gates362896.json',gates['362896'])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','ACTUALBRIEF.md','NETWORK-STOP.md','NEW-UNAVAILABLE.json','search-response-1.txt','search-response-2.txt','search-response-3.txt','get-simplex.json','get-simplex-final.json','get-simplex-metadata.json','get-quantum-pdf.json','get-correction.json','get-fritsch.json']:shutil.copyfile(A/f,L/'inputs'/f)
sim=sorted(q for q in (A/'sources').iterdir() if q.name.startswith('simplex') and q.is_file());assert sim
for q in sim:shutil.copyfile(q,L/'inputs'/q.name)
shutil.copyfile(ROOT/'accepted57-review-context.json',L/'inputs/accepted57-scopes.json')
prior=P/'spherical-error-monotonicity-source-review-sol-r1/inputs/prior39-routing.json';assert sha(prior)=='6493e29137d286242b09d96f97dfe39a9ca5146a8d73bcfa8177e4705d6aaff3';shutil.copyfile(prior,L/'inputs/prior39-scopes.json')
save(L/'reservation.json',dict(ids=[362896],rows=[literal],purpose='Independent ordinary proof, literal/source, classical prior-art and significance review of the simplex 3-design nonexistence proposal; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
t=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in t.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
detail='''TARGET: MathDB 362896, nonexistence of d-point simplex 3-designs. Primary source: Gonzalez Avella, Czartowski, Goyeneche and Zyczkowski, Quantum 9, 1763 (2025), DOI 10.22331/q-2025-06-04-1763, Definition 4, Eq. 5 and Conjecture 7, supplied in inputs as the simplex files; the arXiv version is 2404.18847. The distinct correction note 2505.05894 is also supplied. The original raw record is inputs/original362896.raw.jsonl.

READ FIRST. inherited-denials.json is about 250 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns, before any other step.

The author FULLCANDIDATE.md is an unreviewed proposal. Root has verified provenance only, with a hand spot check of the two cubic norm formulas that does not replace yours. Disclosed mechanism: first and second moments force the d centred points to have a regular-simplex Gram matrix, by a finite sum of squares; hence the empirical third-moment array has a fixed squared Frobenius norm; it is compared with the squared norm of the central third-moment tensor of the flat Dirichlet measure, and equality forces d^2=0. Reconstruct the proof or a precise GAP yourself before opening FULLCANDIDATE.md or DORMANT-SOL-FORMAL-PLAN.md.

LITERAL AND SOURCE BINDING. Settle each from the actual glyphs in the final paper, not from the author's summary:
1. Compare the MathDB literal word for word with Conjecture 7 and Definition 4. Establish what a d-point simplex t-design is: the simplex and its dimension, the flat probability measure and its normalization, equal weights versus general weights, whether repeated points are allowed, and whether polynomials are all those of total degree at most t or only homogeneous ones of degree t.
2. Establish exactly which d are claimed, what the source itself proves (including d=3 and the t>=4 rank bound), and whether anything in the source restricts the points or the class of constructions so that the universal negative claim differs from the literal.
3. Render and view the pages carrying Definition 4, Eq. 5 and Conjecture 7.

ORDINARY AUDIT. Check at least: the simplex moment formulas including the normalization of the flat measure; the passage from degree at most 3 matching to the mean, covariance and central third moments; the identity for the second moment matrix and the sum-of-squares route to the Gram matrix, with every finite-sum interchange; the norm identity expressing the Frobenius norm through cubes of inner products; the formula for S and for T_cont at all three index patterns; the exact arithmetic of (A), (B) and the final equation; and the boundary cases d=2, where the proof must not apply, and small d. The proposal claims the result even for real coordinates without positivity; confirm that is right and not a sign of an error. Say whether the Frobenius invariant truly captures all mixed cubic constraints in the direction used, namely that equal tensors have equal norms.

PRIOR ART IS THE DECISIVE GATE. Classical cubature theory studies minimal degree-three formulas with n+1 nodes in n dimensions and equal-weight Chebyshev-type formulas, and this result may already be contained there, or be an immediate consequence. Fritsch 1970, Math. Comp. 24, is closed: its DOI chain returned a challenge page, and you must not retry or recover it by any route. Using your search budget, look for distinct primary sources: Stroud, Mysovskikh, Moeller and later work on minimal degree-three formulas and equal-weight formulas on the simplex, and the predecessor arXiv 1308.3188 (Baladram) which is unread and not closed. Read any genuinely applicable primary theorem and proof you can reach through a permitted URL. If you find an applicable theorem, give the complete bridge. If the closed Fritsch paper remains the only specific applicable lead, record a precise HOLD naming it. A bounded nonmatch is not a worldwide novelty claim.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, known results, parameter instances and corrections, and shortness alone is not an exclusion. Give the strongest case on each side. Negative: a short tensor-norm comparison may be a standard cubature obstruction applied to one region, and the conjecture may be known to specialists. Positive: this is a published 2025 all-dimension conjecture left open by its authors after a heuristic and a d=3 argument, and the proof handles all mixed cubic constraints at once rather than changing one estimate in an existing proof. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR KNOWN, with reasons. Root alone adjudicates.

FAMILY AND FORMAL. Compare against all supplied 57+39 scopes. Do not run Lean. Record which formal infrastructure is unpaid, separating the elementary finite-sum algebra from the flat simplex measure and its moment formulas, and give a realistic feasibility estimate, noting that heavy measure-theory imports are currently hard to kernel-check here. Write a dormant Sol formal brief only if the scientific gates prospectively survive.

Author proposal is not an independent PASS. Credit 0; campaign 57/60 unchanged.
'''
peers=['high-girth-ur-matching-formal-sol-r8','interval-kwidth-limit-source-review-sol-r1'];task=common.format(lane=L,id=362896,peers=', '.join(peers))+'\nTARGET-SPECIFIC INDEPENDENT REVIEW\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+list((L/'inputs').iterdir());save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=362896,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'simplex-three-design-review-r1-ready.json',ready);save(ROOT/'selection-routing-simplex-three-design-review-r1.json',dict(ids=[362896],sources=[literal['source_url']],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
save(ROOT/'r519-intake-report.json',dict(utc=now,files=209,frozen=13,corpus_bindings=20,history_names=896,review_ready=ready,queued_for_review=[341690],credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r519_manifest=209,frozen=13,corpus=20,history=896,review=ready,sources=[q.name for q in sim],queued=[341690],credit=0,accepted_new=57)))
