"""Root documentary verification of r534 and preparation of independent adversarial qualifications of 368315, 342017 and 352303. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==58
A=P/'expanded-corpus-r534';B=P/'expanded-corpus-r533';V=P/'regular-palm-locating-primary-qualification-claude-r1'
names3={368315:'rowmotion-typical-orbit-primary-qualification-claude-r1',342017:'smooth-arithmetical-primary-qualification-claude-r1',352303:'biharmonic-tree-primary-qualification-claude-r1'}
for n in names3.values():assert not (P/n).exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==187==m['count']
fnames=set()
for n,h in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;fnames.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==h,n
aex=m['self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_manifest.output.txt','seal_manifest.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==fnames|set(aex)
frozen(A,13);arec=receipts(A,{'get_core_345953608.receipt.json':1})
route=read(ROOT/'selection-routing-r534.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];res=read(A/'results.json');gates=res['gates'];bind=read(A/'literal-bindings.json')['bindings'];assert len(ids)==len(gates)==len(bind)==20 and set(ids)==set(map(int,gates))==set(map(int,bind))
sources={};raws={}
for key,v in bind.items():
 q=Path(v['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(v['line_one_based'])-1];assert raw.endswith(b'\n') and v['newline_terminated'] is True and dg(raw)==v['raw_line_sha256_including_newline']
 obj=json.loads(raw);tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1 and obj['mathdb_id']==int(key) and dg(tokens[0])==v['raw_statement_token_sha256'] and obj['statement']==v['decoded_statement'] and dg(obj['statement'].encode())==v['decoded_statement_sha256'];sources[key]=obj['source_url'];raws[key]=raw
abudget=search(A,3,3,3,9,['searches/search-1.response.txt','searches/search-2.response.txt','searches/search-3.response.txt'])
ae=guard(A,sorted(A.glob('plans/get-*.json')),ids,dict(attempt=8,success=7,unavailable=1),7)
un=next(e for e in ae if e['event']=='unavailable');assert un['status']==403 and 'core.ac.uk' in un['url']
for name in read(A/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
fc=(A/'FULLCANDIDATE.md').read_text();ia=fc.index('# PART A');ib=fc.index('# PART B');dp=(A/'DORMANT-SOL-FORMAL-PLAN.md').read_text();pa=dp.index('## Target A');pb=dp.index('## Target B')
fb=(B/'FULLCANDIDATE.md').read_text();b1=fb.index('# PART B. MathDB 352303');b2=fb.index('# PART C. MathDB 381964');db=(B/'DORMANT-SOL-FORMAL-PLAN.md').read_text()
bb=read(B/'literal-bindings.json')['352303'];qb=Path(bb['chunk']);rb=qb.read_bytes().splitlines(keepends=True)[int(bb['line_one_based'])-1];assert dg(rb)==bb['raw_line_with_newline_sha256']
bled=[json.loads(l) for l in (B/'guard-ledger.jsonl').read_text().splitlines()];src352=[e['destination'] for e in bled if e['event']=='success' and '2110.09931' in e['url']];assert src352
for f in ['2505.04000.pdf','1903.01398.pdf','2007.15100.pdf']:assert (A/'sources'/f).is_file()

ass='r534 two author-complete proofs, neither independently reviewed. 368315 typical rowmotion orbit: r(n) = 1 - O_m(1/n) for every fixed m, by rotation of 2m marks with a fixed noncrossing matching and a hidden zone, importing source Theorem 1.1; the source section 4.1 outlines a good-family plan. 342017 smooth arithmetical structures: N(m,n) is quasi-polynomial of degree m-1 and N(m,n)/binom(m+n-1,n) -> alpha_(m-1), through a Stern-Brocot reformulation and a ten-state transducer; a boundary error in source Table 2 is noted with no credit; "same rate" is informal and is read as fixed m. Both routed to independent adversarial qualification. 334707, 388669 and 320923 are public, 340378 and 376374 recorded solved in the literal, zero; thirteen parked. Seventeen assigned source works unread. Verified 187 manifest files, 20 corpus bindings, 13 frozen, 8 GET hops (7 PDF, 1 HTTP 403), 3 searches / 3 strings with responses saved. Credit 0, 58/80.'
work='core.ac.uk PDF 345953608, identity unread, possibly the Integers final of Glass and Wagner';fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 403; no retry.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=187,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,model='claude-opus-5-5',scientific_summary=ass,root_disposition='TWO_AUTHOR_COMPLETE_CANDIDATES_ROUTED_TO_INDEPENDENT_ADVERSARIAL_QUALIFICATION',credit=0,accepted_new=58,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r570.json');den['utc']=now;den['root_r534_scope']=ass;den['root_core_403_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un.get('url_key') or un['url']});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'core.ac.uk/download/345953608'})
den['records'].append(dict(url=un['url'],reason=dict(status=403,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r534-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r571.json';save(denpath,den)

tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
for a,b in [('Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed.','Use ONLY Claude Opus 5.5, high effort; GPT subagents are barred for now.'),('Campaign57/60','Campaign58/80'),('Credit0,57/60 unchanged','Credit0,58/80 unchanged'),('conditional dormant Sol formal brief','conditional dormant formal brief'),('Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. ','Render PDF pages with pdftoppm and extract text with pdftotext by subprocess under your runner. ')]:
 assert common.count(a)==1,a;common=common.replace(a,b)
HEAD='''TARGET: independent adversarial qualification of MathDB {id}. {what}

Campaign background. Seven full proofs were excluded after a deeper check found a generic route or a reduction to the source, an explicit counterexample was declined by the user as coefficient tuning, a correct exact-constant theorem was excluded as a re-indexing of the source count, and result 58 passed this kind of review. Your job is to try hard to exclude this one, and to report honestly if you cannot.

TOOLS. You are Claude Opus 5.5. Your web search is WebSearch; load it through ToolSearch if deferred and use standard mode. Run every local command through your own runner as the common text says, and do not use your own file-reading or web-fetching tools on lane files, with one exception: you may use Read to view PNG pages you rendered yourself. Let every true exit code stand. Read charge_search.py and source_get_guard.py to see how they are invoked before using them.

READ FIRST. inherited-denials.json is about 300 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns.

PROOF. Reconstruct the proof or a precise gap yourself before opening inputs/author-candidate.md. The mechanism above is disclosed; what you must reconstruct is the argument. Then audit the author against your reconstruction.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
{questions}
{last}. Spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json.

If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so, and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Assess inputs/author-formal-plan.md and say what the literal Lean endpoint should be.

Author proposal is not acceptance. Credit 0; campaign 58/80 unchanged.
'''
specs={368315:dict(what='The conjecture (Lafreniere, Lewis and coauthors, arXiv 2505.04000, Conjecture 4.1) says that for every positive m the fraction r(n) of interval-closed sets of [m]x[n] in rowmotion orbits of size m+n+1 tends to 1. The author proposal claims r(n)=1-O_m(1/n), by showing that on generic interval-closed sets rowmotion is rotation by 1 of 2m marks on a cycle of length m+n+1 carrying a fixed noncrossing matching, with a hidden zone of m-1 positions, and it imports source Theorem 1.1.',questions='''1. What exactly does the source's Section 4.1 establish and leave open? Is the proposal a routine completion of a plan the authors outlined? Separate what they state as proved, as conditional and as hoped for.
2. Is source Theorem 1.1 used correctly, and is it needed? Check the bracketing and the transitions, the cases m=1 and small n, and the author's claim that the source's orbit statement as worded fails at m=1 for even n>=6.
3. Does general rowmotion or promotion theory imply this, for example results on interval-closed sets, toggle groups, resonance, or homomesy? Search for follow-ups to arXiv 2505.04000 and for other proofs, and read any applicable body through a permitted URL.
4. Is there a short generic argument that most interval-closed sets have a fixed orbit size?''',last=5,files=['2505.04000.pdf'],lane=A,part=fc[ia:ib],plan=dp[pa:pb],raw=raws['368315']),
342017:dict(what='The conjecture (Glass and Wagner, arXiv 1903.01398, Conjecture 1.4) says that the number of smooth arithmetical structures on the path with a doubled edge grows at the same rate as binom(m+n-1,n). The author proposal claims N(m,n) is quasi-polynomial in n of degree m-1, and that N(m,n)/binom(m+n-1,n) tends to alpha_(m-1) = (15/4)(5/2)^(m-1) + (1/4)(-1/2)^(m-1), through a Stern-Brocot reformulation and a ten-state coupled doubling transducer.',questions='''1. Literal first: "same rate" is informal. Decide what the record claims, whether fixed m with n to infinity is the right reading, and whether the author's constant goes beyond it. Check the author's statement that a uniform two-variable reading is false.
2. Is the bare growth statement a routine extension of the source's cases m=1,2,3 by iterating its casework? If so, does the exact constant change that? The credit question is whether the literal statement alone is routine.
3. Check the transducer, the automaton and the pole analysis, the agreement with the source's theorems, and the claimed error in source Table 2.
4. Search for later work on smooth arithmetical structures and for the Integers final of Glass and Wagner. That one identified core.ac.uk artifact is closed (see inherited-denials.json); do not recover it by another route. If the final remains unread, say what that leaves open. Keyes and Reiter (inputs/sources/2007.15100.pdf) mention the conjecture; read what they say.''',last=5,files=['1903.01398.pdf','2007.15100.pdf'],lane=A,part=fc[ib:],plan=dp[pb:],raw=raws['342017']),
352303:dict(what='The conjecture (Lin, The biharmonic index of connected graphs, arXiv 2110.09931, Conjecture 5.3) says that among trees on n>=5 vertices, BH is minimized uniquely by the star and maximized uniquely by the path, where BH(G) = n times the sum of 1/lambda_i^2 over nonzero Laplacian eigenvalues. The author proposal claims BH(T)=N(T)/n with N(T) an explicit sum over edge pairs from the inverse edge Laplacian, and proves both bounds, the upper one by a pendant-path shift.',questions='''1. Is this routine? The inverse edge-Laplacian formula is classical and pendant-path shifting is the standard tool of this area. Does a known monotonicity theorem, for example on Laplacian coefficients (Mohar) or on tree shifts (Csikvari), or a majorization or Schur-convexity result, give the statement? The author says the sum of 1/lambda^2 is a difference of two quantities that both increase toward the path, so coefficient monotonicity fails; check that.
2. Check the upper-bound algebra in full, in particular the claimed identity N(T')-N(T) = (P^2-q^2)(2S+(4/3)tPq) + t^2(U(P)-U(q)), and the formula against the source's double-star Theorem 5.1.
3. Search for prior proofs, including Wei, Li and Yang arXiv 2110.02656, the published form of Lin's paper, and work on the sum of squared reciprocal Laplacian eigenvalues of trees, and on biharmonic or Kirchhoff-type extremal problems. Read any applicable body through a permitted URL.
4. Does the same proof give a one-parameter family containing the target, and if so does that make the target an instance?''',last=5,files=[Path(d).name for d in src352],lane=B,part=fb[b1:b2],plan=db,raw=rb)}
peers=['zeckendorf-games-formal-deepseek-r1','expanded-corpus-r535'];ready={}
for mid,sp in specs.items():
 L=P/names3[mid];L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
 for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py','model-policy.json']:shutil.copyfile(V/h,L/h)
 shutil.copyfile(denpath,L/'inherited-denials.json')
 (L/f'inputs/original{mid}.raw.jsonl').write_bytes(sp['raw']);literal=json.loads(sp['raw']);save(L/f'inputs/literal{mid}.json',literal)
 (L/'inputs/author-candidate.md').write_text(sp['part']);(L/'inputs/author-formal-plan.md').write_text(sp['plan'])
 for f in sp['files']:
  q=sp['lane']/'sources'/f;assert q.is_file(),q;shutil.copyfile(q,L/'inputs/sources'/f)
 for n in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(V/'inputs'/n,L/'inputs'/n)
 save(L/'reservation.json',dict(ids=[mid],rows=[literal],purpose='Independent adversarial qualification; no formal tools'));(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
 task=common.format(lane=L,id=mid,peers=', '.join(peers))+'\nTARGET-SPECIFIC QUALIFICATION\n'+HEAD.format(id=mid,what=sp['what'],questions=sp['questions'],last=sp['last'])
 (L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
 ready[mid]=dict(utc=now,lane=str(L),mathdb_id=mid,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='claude-opus-5-5',effort='high',accepted_new=58,target_new=80,credit=0,protected_peers=peers,latest_denials=str(denpath))
 save(ROOT/f'qualification-{mid}-ready.json',ready[mid]);save(ROOT/f'selection-routing-qualification-{mid}.json',dict(ids=[mid],sources=[literal['source_url']],lane=str(L),task_sha256=ready[mid]['task_sha256'],metadata_only=True))
save(ROOT/'qualification-queue-20261109.json',dict(utc=now,order=[368315,342017,352303],launched=[]))
print(json.dumps(dict(r534_manifest=187,frozen=13,corpus=20,ready={k:(v['lane'].rsplit('/',1)[-1],v['frozen_bindings']) for k,v in ready.items()},credit=0,accepted_new=58)))
