"""Root documentary verification of r532 and preparation of the independent adversarial qualification of 344875. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r532';Q=P/'transitive-bunkbed-primary-qualification-sol-r2';L=P/'regular-palm-locating-primary-qualification-claude-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==177==m['file_count'] and m['nonzero_receipts']==[]
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal-manifest.output.txt','seal-manifest.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r532.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];res=read(A/'results.json');gates=res['results'];bind=read(A/'corpus-bindings.json');rows=bind['rows'];assert len(ids)==len(gates)==len(rows)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in rows} and res['qualified_survivors_claimed']==0
sources={};raws={}
for v in rows:
 q=Path(v['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(v['line_one_based'])-1];assert raw.endswith(b'\n') and v['has_trailing_newline'] is True and dg(raw)==v['raw_line_sha256_with_newline']
 obj=json.loads(raw);tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1 and obj['mathdb_id']==int(v['id']) and dg(tokens[0])==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_decoded_sha256'];sources[str(v['id'])]=obj['source_url'];raws[str(v['id'])]=raw
 assert gates[str(v['id'])]['literal_statement']==obj['statement']
assert all(str(g['credit'])=='0' for g in gates.values())
abudget=search(A,3,3,3,9,['search-responses/search-1.txt','search-responses/search-2.txt','search-responses/search-3.txt'])
ae=guard(A,sorted(A.glob('plans/get-*.json')),ids,dict(attempt=9,success=9),8)
for name in read(A/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])
for f in ['FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','sources/1912.05775.pdf','sources/1912.05775.txt','sources/1912.05775.abs.html']:assert (A/f).is_file(),f
for f in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py']:assert (Q/f).is_file(),f

ass='r532 one author-complete candidate, not claimed as qualified. 344875: the printed conjecture chi_L(S_n(k)) = (1+o(1)) ((k-1)/2) (4n)^(1/k) is refuted for every k>=4, and the true leading constant beta_k = (l^l u^u)^(1/k), l=floor(k/2), u=ceil(k/2), is determined for every k with bounded additive error; beta_4=2 against the printed 2.1213. The author records a serious routine-extension objection: the lower bound is the general-k form of the source k=3 count, and the k=4 witness alone resembles coefficient tuning. Root routes it to an independent adversarial qualification. 330067 refuted through a covering-array limit, excluded as routine by the author. 339249 clause (1) routine, clause (2) unproved. 364797 settled in its own source. 330915, 328539, 373109, 365985 parked; 345483 lower bound only. Thirteen assigned source works unread. Verified 177 manifest files, 20 corpus bindings, 13 frozen, 9 GET successes (8 PDF), 3 searches / 3 strings with responses saved. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=177,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,model='claude-opus-5-5',scientific_summary=ass,root_disposition='ONE_AUTHOR_COMPLETE_CANDIDATE_ROUTED_TO_INDEPENDENT_ADVERSARIAL_QUALIFICATION',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r565.json');den['utc']=now;den['root_r532_scope']=ass
save(P/'expanded-corpus-r532-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r566.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py']:shutil.copyfile(Q/h,L/h)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'));shutil.copyfile(denpath,L/'inherited-denials.json')
(L/'inputs/original344875.raw.jsonl').write_bytes(raws['344875']);literal=json.loads(raws['344875']);save(L/'inputs/literal344875.json',literal);save(L/'inputs/provenance344875.json',next(v for v in rows if str(v['id'])=='344875'))
shutil.copyfile(A/'FULLCANDIDATE.md',L/'inputs/author-FULLCANDIDATE.md');shutil.copyfile(A/'DORMANT-SOL-FORMAL-PLAN.md',L/'inputs/author-DORMANT-FORMAL-PLAN.md')
for n in ['1912.05775.pdf','1912.05775.txt','1912.05775.abs.html']:shutil.copyfile(A/'sources'/n,L/'inputs/sources'/n)
for n in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(Q/'inputs'/n,L/'inputs'/n)
save(L/'reservation.json',dict(ids=[344875],rows=[literal],purpose='Independent adversarial qualification of the regular palm locating-chromatic result; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
for a,b in [('Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed.','Use ONLY Claude Opus 5.5, high effort; GPT subagents are barred for now.'),('Campaign57/60','Campaign57/80'),('Credit0,57/60 unchanged','Credit0,57/80 unchanged'),('conditional dormant Sol formal brief','conditional dormant formal brief'),('Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. ','Render PDF pages with pdftoppm and extract text with pdftotext by subprocess under your runner. ')]:
 assert common.count(a)==1,a;common=common.replace(a,b)
assert 'GPT-6.1' not in common and '.codex' not in common
detail='''TARGET: independent adversarial qualification of MathDB 344875, the regular palm conjecture of Hafidh and Baskoro (arXiv 1912.05775v2, Conjecture 5.1): for k >= 4, chi_L(S_n(k)) = (1+o(1)) ((k-1)/2) (4n)^(1/k). This is the first independent review. The author proposal claims the conjecture is false for every k >= 4 and that the true leading constant for every k is beta_k = (l^l u^u)^(1/k), with l = floor(k/2) and u = ceil(k/2), by a level-window count and a construction confining each colour to two adjacent positions. The author records a serious routine-extension objection and does not claim the result qualifies.

Campaign background. Five full proofs were excluded after a deeper check found a generic route or a complete source reduction. The user declined an explicit counterexample because a two-term parameter family made it ordinary coefficient tuning, and root excluded a correct short proof that added a second prime to the source's own Dirichlet step. One candidate did survive this kind of review. Your job is to try hard to exclude this one, and to report honestly if you cannot.

TOOLS. You are Claude Opus 5.5. Your web search is WebSearch; load it through ToolSearch if deferred and use standard mode. Run every local command through your own runner as the common text says, and do not use your own file-reading or web-fetching tools on lane files, with one exception: you may use Read to view PNG pages you rendered yourself. Let every true exit code stand; do not wrap a failing step so its receipt shows exit 0. Read charge_search.py and source_get_guard.py to see how they are invoked before using them.

READ FIRST. inherited-denials.json is over 290 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns.

PROOF. Reconstruct the proof or a precise gap yourself before opening inputs/author-FULLCANDIDATE.md. The mechanism above is disclosed; what you must reconstruct is the argument. Then audit the author against the checklist in its section 8: the distance formula when the depth-D_t vertex lies on the same arm and the case of the hub colour; the strict inequality in the construction; the sum bounds in both parities; the convention that a colouring is proper with nonempty classes, against what the source actually says; coverage and the range of n; and the meaning of (1+o(1)) with k fixed.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
1. Is the all-k result a routine extension of the source's own k=2 and k=3 arguments? Read the source's Theorems 5.1 to 5.3 and proofs carefully. State exactly what the source's k=3 count and construction are, and what must be added for general k. If the general count is the source's count with a change of index and the construction is a direct generalization, say so and give the bridge.
2. Is the refutation only an optimization correction of an unproved guess? Does the printed constant correspond to a uniform allocation as the author reconstructs, and does the source give any reason for it? Separate the two possible units of credit: the k=4 witness and the all-k exact-constant theorem. Decide which, if either, would be more than coefficient tuning or a correction.
3. Is it known or implied? Search for later work on locating chromatic numbers of palms, spiders, caterpillars and trees with fixed diameter or arm length, for asymptotic formulas and for any final or corrected version of Hafidh and Baskoro. Look for a general theorem on locating colourings or on identifying codes or metric-type invariants of spiders that would imply this. Read any applicable body through a permitted URL. A bounded nonmatch is not a worldwide novelty claim.
4. Is there a shorter generic argument for the leading constant, for example through a general theorem about locating codes in trees of bounded depth?
5. Spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json, in particular any locating or metric-dimension style result.

If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so, and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Say whether the dormant plan's k=4 endpoint is the right literal target, and what the all-k theorem would add.

Author proposal is not acceptance. Credit 0; campaign 57/80 unchanged.
'''
peers=['transitive-bunkbed-formal-independent-review-claude-r1','transitive-bunkbed-manuscript-deepseek-r1'];task=common.format(lane=L,id=344875,peers=', '.join(peers))+'\nTARGET-SPECIFIC QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=344875,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='claude-opus-5-5',effort='high',accepted_new=57,target_new=80,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'palm-qualification-r1-ready.json',rdy);save(ROOT/'selection-routing-palm-qualification-r1.json',dict(ids=[344875],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps(dict(r532_manifest=177,frozen=13,corpus=20,next={k:rdy[k] for k in ['lane','task_sha256','frozen_bindings']},credit=0,accepted_new=57)))
