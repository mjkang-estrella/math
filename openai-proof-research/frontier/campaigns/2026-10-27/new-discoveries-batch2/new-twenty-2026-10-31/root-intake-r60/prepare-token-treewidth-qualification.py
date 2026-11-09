"""Root preparation of the independent adversarial qualification of 362080. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==58
A=P/'expanded-corpus-r537';V=P/'regular-palm-locating-primary-qualification-claude-r1';mid=362080;L=P/'token-treewidth-primary-qualification-claude-r1';assert not L.exists()
v=read(A/'corpus-bindings.json');v=v.get('bindings',v.get('rows',v)) if isinstance(v,dict) and ('bindings' in v or 'rows' in v) else v;v=v[str(mid)] if isinstance(v,dict) else next(y for y in v if str(y.get('id',y.get('mathdb_id')))==str(mid))
raw=Path(v['chunk_path']).read_bytes().splitlines(keepends=True)[int(v['one_based_line'])-1];assert dg(raw)==v['raw_line_with_newline_sha256'];literal=json.loads(raw);assert literal['mathdb_id']==mid
denpath=ROOT/'inherited-denials-r578.json';assert denpath.is_file()
L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py','model-policy.json']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json');(L/f'inputs/original{mid}.raw.jsonl').write_bytes(raw);save(L/f'inputs/literal{mid}.json',literal)
shutil.copyfile(A/'FULLCANDIDATE.md',L/'inputs/author-candidate.md');shutil.copyfile(A/'DORMANT-SOL-FORMAL-PLAN.md',L/'inputs/author-formal-plan.md');shutil.copyfile(A/'sources/token-graph-2402.17962.pdf',L/'inputs/sources/token-graph-2402.17962.pdf')
for n in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(V/'inputs'/n,L/'inputs'/n)
save(L/'reservation.json',dict(ids=[mid],rows=[literal],purpose='Independent adversarial qualification; no formal tools'));(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
for a,b in [('Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed.','Use ONLY Claude Opus 5.5, high effort; GPT subagents are barred for now.'),('Campaign57/60','Campaign58/80'),('Credit0,57/60 unchanged','Credit0,58/80 unchanged'),('conditional dormant Sol formal brief','conditional dormant formal brief'),('Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. ','Render PDF pages with pdftoppm and extract text with pdftotext by subprocess under your runner. ')]:
 assert common.count(a)==1,a;common=common.replace(a,b)
detail='''TARGET: independent adversarial qualification of MathDB 362080, the treewidth order conjecture for token graphs of trees (arXiv 2402.17962, Conjecture 20): for fixed k and every tree G on n vertices, tw(F_k(G)) is Theta(n^(k-1)). The author proposal claims an upper bound (2k-1)n^(k-1) by removing token sets containing a centroid, and a lower bound n^(k-1)/(32 k^(2k+3) 2^k) for n >= 8k^2 from a balanced separator and hand-off route congestion, with constants depending only on k. The author itself says the same argument gives c_k n^(k-1) <= tw(F_k(G)) <= C_k (tw(G)+1) n^(k-1) for every connected G, so trees are just where the two bounds meet, and it does not claim the result qualifies.

Campaign background. Eight full proofs were excluded after a deeper check found a generic route or a reduction, including a limit formula that was an instance of a general law, and a theorem completely reduced to classical theory the author had not noticed. An explicit counterexample was declined by the user as coefficient tuning. Result 58 passed this kind of review. Your job is to try hard to exclude this one, and to report honestly if you cannot.

TOOLS. You are Claude Opus 5.5. Your web search is WebSearch; load it through ToolSearch if deferred and use standard mode. Run every local command through your own runner as the common text says, and do not use your own file-reading or web-fetching tools on lane files, with one exception: you may use Read to view PNG pages you rendered yourself. Do not pipe runner output through other commands outside the runner. Let every true exit code stand. Save each native search response as the very next tool call, and do not end your turn between a search and its save. Read charge_search.py and source_get_guard.py to see how they are invoked before using them.

READ FIRST. inherited-denials.json is about 320 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges.

PROOF. Reconstruct the proof or a precise gap yourself before opening inputs/author-candidate.md. The mechanism above is disclosed; what you must reconstruct is the argument. Then audit the author, in particular the route counting and the balanced-separator step, whether the constants really do not depend on the tree, the case where k is near n, and the literal's range 1 <= k <= n-1 with k fixed.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
1. The author's general bound for all connected G: is it correct, and does it make the tree theorem a parameter instance of a general law in the sense that excluded earlier results? Decide this explicitly, and say whether the general law is itself new or known.
2. Is there a shorter route? For example a monotonicity or minor relation between token graphs of a tree and token graphs of a path or star, an embedding of a product of paths into F_k(T), or a general lower bound for treewidth from vertex expansion or from the Johnson-like structure of F_k. If the source's star and path arguments extend by a routine change, give the bridge.
3. Read the source's Lemma 9, its spectral bound and its star bramble in full. Verify the author's claims about what they cannot reach.
4. Search for prior work: treewidth or separators of token graphs, symmetric powers of graphs, double vertex graphs and k-subset graphs, and any follow-up to arXiv 2402.17962. Read any applicable body through a permitted URL.
5. Spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json.

If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so, and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Assess inputs/author-formal-plan.md and say what the literal Lean endpoint should be.

Author proposal is not acceptance. Credit 0; campaign 58/80 unchanged.
'''
peers=['zeckendorf-games-formal-deepseek-r1','biharmonic-tree-formal-deepseek-r1'];task=common.format(lane=L,id=mid,peers=', '.join(peers))+'\nTARGET-SPECIFIC QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=mid,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='claude-opus-5-5',effort='high',accepted_new=58,target_new=80,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/f'qualification-{mid}-ready.json',rdy);save(ROOT/f'selection-routing-qualification-{mid}.json',dict(ids=[mid],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps({k:rdy[k] for k in ['lane','task_sha256','frozen_bindings']}))
