"""Root documentary verification of r533 and preparation of the independent adversarial qualification of 347063. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==58
A=P/'expanded-corpus-r533';V=P/'regular-palm-locating-primary-qualification-claude-r1';Q=P/'transitive-bunkbed-primary-qualification-sol-r2';L=P/'zeckendorf-games-primary-qualification-claude-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==195==m['file_count']
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_manifest.output.txt','seal_manifest.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'get_381964_final.receipt.json':1})
route=read(ROOT/'selection-routing-r533.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');bind=read(A/'literal-bindings.json');assert len(ids)==len(gates)==len(bind)==20 and set(ids)==set(map(int,gates))==set(map(int,bind))
sources={};raws={}
for key,v in bind.items():
 q=Path(v['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(v['line_one_based'])-1];assert raw.endswith(b'\n') and v['ends_with_newline'] is True and dg(raw)==v['raw_line_with_newline_sha256']
 obj=json.loads(raw);tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1 and obj['mathdb_id']==int(key) and dg(tokens[0])==v['raw_statement_token_sha256'] and obj['statement']==v['decoded_statement'] and dg(obj['statement'].encode())==v['decoded_statement_sha256'];sources[key]=obj['source_url'];raws[key]=raw
abudget=search(A,3,3,3,9,['searches/search-1-response.txt','searches/search-2-response.txt','searches/search-3-response.txt'])
ledger=[json.loads(l) for l in (A/'guard-ledger.jsonl').read_text().splitlines()];pdfs=sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in ledger if e['event']=='success')
ae=guard(A,sorted(A.glob('plans/get-*.json')),ids,dict(attempt=12,success=10,redirect=1,unavailable=1),pdfs)
un=next(e for e in ae if e['event']=='unavailable');assert un['status']==403 and 'mdpi.com' in un['url']
for name in read(A/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])
fc=(A/'FULLCANDIDATE.md').read_text();ia=fc.index('# PART A. MathDB 347063');ib=fc.index('# PART B. MathDB 352303');ic=fc.index('# PART C. MathDB 381964');assert 0<ia<ib<ic
dp=(A/'DORMANT-SOL-FORMAL-PLAN.md').read_text()
src347=[e['destination'] for e in ae if e['event']=='success' and '2006.16457' in e['url']];assert src347

ass='r533 three author-complete proofs, none independently reviewed. 347063 Zeckendorf games: Split Smallest takes phi^2 n + O(log^2 n) moves and Combine Smallest takes c n + O(sqrt n log n) with c = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.20648; the corpus literal mistranscribes the start position; no search was spent on this target. Routed to independent adversarial qualification. 352303 extremal biharmonic index of trees: full conjecture via BH(T)=N(T)/n and a pendant-path shift, strong routine objection; queued for qualification. 381964 spectrum on K_{n+1}: author recommends exclusion, a multiplicity-free symmetry forces the block form, zero. 372171 and 363473 settled in their own sources. 346227 domain correction. 349418 and 346406 parked with gaps; twelve parked after the literal only. Disclosed: two oversized displays were persisted outside the lane and not opened, one shell cd preceded the first charge, a placeholder in one gate field was repaired before sealing. Verified 195 manifest files, 20 corpus bindings, 13 frozen, 12 GET hops (10 successes, 1 redirect, 1 HTTP 403), 3 searches / 3 strings with responses saved. Credit 0, 58/80.'
na=read(A/'NEW-UNAVAILABLE.json');work='Cushing, Kamtue, Liu, Muench, Peyerimhoff, Snodgrass, Bakry-Emery curvature sharpness and curvature flow in finite weighted graphs: implementation, Axioms 12 (2023) 577, arXiv 2212.12401'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 403; no retry.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=195,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,model='claude-opus-5-5',scientific_summary=ass,root_disposition='TWO_AUTHOR_COMPLETE_CANDIDATES_ROUTED_TO_INDEPENDENT_ADVERSARIAL_QUALIFICATION',credit=0,accepted_new=58,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r568.json');den['utc']=now;den['root_r533_scope']=ass;den['root_axioms_403_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un.get('url_key') or un['url'],'arxiv.org/abs/2212.12401','arxiv.org/pdf/2212.12401'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'2212.12401','10.3390/axioms12060577'})
den['records'].append(dict(url=un['url'],reason=dict(status=403,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r533-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r569.json';save(denpath,den)

L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py','model-policy.json']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json')
(L/'inputs/original347063.raw.jsonl').write_bytes(raws['347063']);literal=json.loads(raws['347063']);save(L/'inputs/literal347063.json',literal);save(L/'inputs/provenance347063.json',bind['347063'])
(L/'inputs/author-candidate-347063.md').write_text(fc[ia:ib]);ra=dp.index('## Route A');(L/'inputs/author-formal-plan-347063.md').write_text(dp[ra:dp.index('## Route',ra+10)])
for d in src347:shutil.copyfile(A/d,L/'inputs/sources'/Path(d).name)
for n in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(V/'inputs'/n,L/'inputs'/n)
save(L/'reservation.json',dict(ids=[347063],rows=[literal],purpose='Independent adversarial qualification of the Zeckendorf game move counts; no formal tools'))
(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
for a,b in [('Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed.','Use ONLY Claude Opus 5.5, high effort; GPT subagents are barred for now.'),('Campaign57/60','Campaign58/80'),('Credit0,57/60 unchanged','Credit0,58/80 unchanged'),('conditional dormant Sol formal brief','conditional dormant formal brief'),('Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. ','Render PDF pages with pdftoppm and extract text with pdftotext by subprocess under your runner. ')]:
 assert common.count(a)==1,a;common=common.replace(a,b)
detail='''TARGET: independent adversarial qualification of MathDB 347063, the linear-growth conjecture for the Split Smallest and Combine Smallest Zeckendorf games (Li, Li, Miller, Mizgerd, Sun, Xia, Zhou, Deterministic Zeckendorf Games, arXiv 2006.16457). The author proposal claims SS(n) = phi^2 n + O(log^2 n) by an exact potential, and CS(n) = c n + O(sqrt(n) log n) with c = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.20648..., by showing that while a pool sits at an even index the whole lower state reduces to one integer rotating modulo a Fibonacci number. The author does not claim credit.

Campaign background. Six full proofs were excluded after a deeper check found a generic route or a reduction to the source, one explicit counterexample was declined by the user as coefficient tuning, and result 58 passed this kind of review. Your job is to try hard to exclude this one, and to report honestly if you cannot.

TOOLS. You are Claude Opus 5.5. Your web search is WebSearch; load it through ToolSearch if deferred and use standard mode. Run every local command through your own runner as the common text says, and do not use your own file-reading or web-fetching tools on lane files, with one exception: you may use Read to view PNG pages you rendered yourself. Let every true exit code stand. Read charge_search.py and source_get_guard.py to see how they are invoked before using them.

READ FIRST. inherited-denials.json is about 300 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges. Save every native search response in the very next tool call after it returns.

LITERAL, FIRST GATE. The MathDB record says the game "starts from the Zeckendorf decomposition of n", which would mean zero moves. The source starts from n copies of F_1. Decide what the record states and whether a proof for the source game resolves it. Quote source Definition 1.1, Theorem 1.2 and Conjecture 1.4 exactly. Note that Theorem 1.2 already gives Theta(n), so the content lies in the two constants. Decide whether phi^2 and "approximately 1.206" are the claim, and whether an exact value of c meets it.

PROOF. Reconstruct the proof or a precise gap yourself before opening inputs/author-candidate-347063.md. The mechanism above is disclosed; what you must reconstruct is the argument. Press hardest on the Combine Smallest part: the exact priority evaluation, the rotation lemma, the chip balance giving F_p - 1 splits per cycle, the assembly across levels with its error term, and the endgame case list. Then audit the author against your reconstruction.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
1. Prior art. No search has been spent on this target. Search for the Fibonacci Quarterly final and follow-up work on deterministic or generalized Zeckendorf games, including exact move counts for these strategies. Read any applicable body through a permitted URL.
2. Is part (a) routine? It is a short potential argument. Is it implied by a source lemma or a known chip-firing result?
3. Is part (b) routine? Is there a generic argument or a reduction to a source theorem that yields the constant? The author says no linear potential can count these splits; check that.
4. Would a specialist learn something new from the constants, or is this an expected computation? Does either part alone qualify, or only both together?
5. Spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json.

If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so, and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Assess inputs/author-formal-plan-347063.md and say what the literal Lean endpoint should be given your answer on the literal.

Author proposal is not acceptance. Credit 0; campaign 58/80 unchanged.
'''
peers=['expanded-corpus-r534','expanded-corpus-r535'];task=common.format(lane=L,id=347063,peers=', '.join(peers))+'\nTARGET-SPECIFIC QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=347063,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='claude-opus-5-5',effort='high',accepted_new=58,target_new=80,credit=0,protected_peers=peers,latest_denials=str(denpath))
save(ROOT/'zeckendorf-qualification-r1-ready.json',rdy);save(ROOT/'selection-routing-zeckendorf-qualification-r1.json',dict(ids=[347063],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
save(ROOT/'queued-qualification-352303.json',dict(utc=now,mathdb_id=352303,reason='Second candidate from r533; start when a slot frees.',source_lane=str(A),raw_sha256=dg(raws['352303']),author_part=[ib,ic],source_url=sources['352303']))
print(json.dumps(dict(r533_manifest=195,frozen=13,corpus=20,pdfs=pdfs,next={k:rdy[k] for k in ['lane','task_sha256','frozen_bindings']},sources=src347,credit=0,accepted_new=58)))
