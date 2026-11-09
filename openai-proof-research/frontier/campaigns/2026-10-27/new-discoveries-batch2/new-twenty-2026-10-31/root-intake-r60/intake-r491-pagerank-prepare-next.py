"""Root documentary integrity and disjoint metadata-only selection; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r491'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(q):return json.loads(q.read_text())
def save(q,d):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r491.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'SHA256-MANIFEST.json');entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==149
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'SHA256-MANIFEST.json','final_manifest.receipt.json','final_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={r['id'] for r in prov}
chunks={};sources={}
for row in prov:
 key=str(row['id']);q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and raw.decode()==row['raw_line'] and (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==row['id']
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_gate']['statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'final_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(A/f'search{i}-response.json').read_text();assert len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in (A/'plans').glob('get-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes'] and q.read_bytes().startswith(b'%PDF')
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://') and set(e['routes'])<=set(map(str,ids))
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=8)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==822
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='378914 actual Gaubert-Katz Theorem4/Example2 supplies complete public nonvertex-apex refutation, zero. 380014 source-own pedigree construction gives 7 versus8 founder counts, correction/adaptation zero. 377306 partial OMCUT adjacency/degree/diameter helpers do not pay unique maximal-degree orbit or complete two-element first-block nonneighbors. 378883 source-own one-matching polynomiality and 378884 actual Aigner all-m two-matching bridge public zero. 378887 actual skew-shape positivity specialization public zero; 377295 actual source partition statistics proof public zero. 377296 distinct later-proof claim remains unread HOLD. Eight original bodies acquired, twelve unread; no full candidate.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=149,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_FULL_SCOPE_SURVIVORS',scientific_summary=summary,process='149 own files,20 corpus raw/token/decoded bindings,13 frozen and822 own saved historical names verified. No external history paths followed. Eight PDF GET successes and3 charged searches/9 queries verified. Outer timeout140 omissions and late enclosing-history reconciliation retained; no early reconciliation or universal process PASS. Exact runner resources/failed receipts retained.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,root_scope='Documentary verification/routing only; no mathematical solving or execution.',terminal_self_exclusions=ex)
# Independent review packet integrity, without running any mathematical tool.
B=P/'pagerank-uniform-source-review-sol-r1';bm=read(B/'SHA256-MANIFEST.json');bf=bm['files'];assert len(bf)==76
for n,h in bf.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=B/n;assert not q.is_symlink() and sha(q)==h,n
bex=bm['exclusions'];assert set(bex)=={'SHA256-MANIFEST.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
ba=set()
for q in B.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():ba.add(str(q.relative_to(B)))
assert ba==set(bf)|set(bex)
fr=read(B/'frozen-inputs.json');assert len(fr)==27
for n,h in fr.items():assert Path(n).is_relative_to(B) and sha(Path(n))==h
for n in ['frozen-before.json','frozen-after.json']:
 v=read(B/n);assert v['count']==27 and v['mismatches']==[]
ready1=read(ROOT/'pagerank-uniform-review-r1-ready.json');assert sha(B/'TASK.txt')==ready1['task_sha256']
literal=read(B/'inputs/literal316846.json');assert json.loads((B/'inputs/original316846.raw.jsonl').read_text())==literal and literal['mathdb_id']==316846
assert read(B/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True)
assert not (B/'guard-ledger.jsonl').exists() and not (B/'search-charges.jsonl').exists()
brec=[]
for q in sorted(B.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(B) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 brec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert len(brec)==17 and read(B/'seal_manifest.receipt.json')['exit']==0 and read(B/'scopes_second.receipt.json')['exit']==1
br=read(B/'review.json');assert br['316846']['acceptance']['credit']==0
pgsummary='316846 independent full ordinary/literal PASS including chain-first-node clause via personally read actual source Theorem12. Controlled inside-row transposition preserves fixed outside rows/accessibility and gives strict uniform resolvent objective improvement. Actual one-row Theorem5 not a complete multirow bridge; Csaji/general optimization leads remain unread navigation. Provisional substantive significance survives, final/current prior/novelty HOLD. Original header2007/footer2022 anomaly retained, cached original and distinct2008 thesis not final equivalence. No new GET/search or formal tools. One documentary KeyError repaired, partial denial display harmless to zero-network work; native/transient/writer peaks unknown.'
brecord=dict(utc=now,source_lane=str(B),manifest_sha256=sha(B/'SHA256-MANIFEST.json'),verified_manifest_files=76,verified_frozen_bindings=27,runner_receipts=brec,review=br,root_disposition='RETAIN_INDEPENDENT_ORDINARY_PASS_ASSIGN_NARROW_PRIMARY_QUALIFICATION',scientific_summary=pgsummary,formal_dispatch=False,credit=0,accepted_new=57,root_scope='Documentary integrity and routing, no independent root mathematical PASS.',terminal_self_exclusions=bex)
delta='Completed r491: '+summary+' 149 files/20 bindings/13 frozen/822 saved history names;8 GET successes,3 searches9 queries; process qualifications retained. '+pgsummary+' Review76 files/27 frozen verified. No new denials.57/60 unchanged.'
den=read(ROOT/'inherited-denials-r501.json');den['utc']=now;den['root_r491_scope']=summary;den['root_pagerank316846_review_scope']=pgsummary;denpath=ROOT/'inherited-denials-r502.json'
# New r492 completion arrived during intake. Verify its independent packet before mutations.
C=P/'expanded-corpus-r492';cm=read(C/'SHA256-MANIFEST.json');cf=cm['files'];assert len(cf)==143
for n,v in cf.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=C/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
cex=cm['terminal_noncircular_self_exclusions'];assert set(cex)=={'SHA256-MANIFEST.json','seal_manifest_final.receipt.json','seal_manifest_final.output.txt'}
ca=set()
for q in C.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():ca.add(str(q.relative_to(C)))
assert ca==set(cf)|set(cex)
cr=read(ROOT/'selection-routing-r492.json');assert sha(C/'TASK.txt')==cr['task_sha256'] and sha(C/'reservation.json')==cr['reservation_sha256']
cfr=read(C/'frozen-inputs.json');assert len(cfr)==13 and all(Path(n).parent==C and sha(Path(n))==h for n,h in cfr.items())
for n in ['frozen-before.json','frozen-after.json']:
 v=read(C/n);assert v['count']==13 and v['mismatches']==[]
cg=read(C/'results.json');cids=read(C/'reservation.json')['ids'];assert len(cg)==len(cids)==20 and set(map(int,cg))==set(cids)
chunks={}
for i in cids:
 row=read(C/'originals'/f'{i}.provenance.json');q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];raw=lines[row['line_1based']-1];obj=json.loads(raw)
 assert h==row['chunk_sha256'] and dg(raw)==row['raw_line_sha256'] and row['newline'] and raw.endswith(b'\n') and raw.decode()==row['raw_line'] and (C/'originals'/f'{i}.jsonl').read_bytes()==raw and obj==cg[str(i)]['record'] and obj['mathdb_id']==i
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==obj['statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256']
crec=[]
for q in sorted(C.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(C) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None
 crec.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(C/'seal_manifest_final.receipt.json')['exit']==0 and read(C/'get_inverse.receipt.json')['exit']==1
cb=read(C/'search-budget.json');assert cb==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (C/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(C/c['plan'])==c['plan_sha256'] and read(C/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=(C/('search-one-response.json' if i==1 else 'search-two-response.json')).read_text();assert len(response)>1000
assert prev==cb and sha(C/'charge_search.py')==sha(ROOT/'charge_search.py')
cp={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in C.glob('get-*-plan.json')};ev=[];prev='0'*64
for i,line in enumerate((C/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);ev.append(e)
 if e['event']=='attempt':assert e['plan_sha256'] in cp and e['url'].startswith('https://') and '/server/api/' not in e['url'] and set(e['routes'])<=set(map(str,cids))
 if e['event']=='success':
  q=C/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes'] and q.read_bytes().startswith(b'%PDF')
cc=collections.Counter(e['event'] for e in ev);assert cc==dict(attempt=6,success=5,unavailable=1);failure=next(e for e in ev if e['event']=='unavailable');assert failure['url_key']=='theoryofcomputing.org/articles/v007a009/v007a009.pdf'
ch=read(C/'history-access.json')['accessed'];cl=read(C/'historical-results-allowlist.json');assert len(ch)==826
for x in ch:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in cl and cl[x['path']]==x['sha256']
csummary='320902 eventual coprime uniqueness,321197 group/list edge equality,317859 switching-equivalent decks retain full-scope gaps.319787 elementary literal negation is source labelled/invariant-algebra correction0.329458 actual matching2610.07943 proof read partially, deep dependencies unaudited specific public-proof HOLD.316525 specific earlier d4 refutation body unread after timeout. Sixteen original bodies unread. No qualified survivor.143 files20 corpus bindings13 frozen826 saved historical names verified;6 GET5PDF1timeout,2 searches6queries. Yielded GET recovery overlap and reading/telemetry qualifications retained.'
crecord=dict(utc=now,source_lane=str(C),manifest_sha256=sha(C/'SHA256-MANIFEST.json'),verified_manifest_files=143,verified_original_bindings=cids,verified_frozen_bindings=13,runner_receipts=crec,guard_events=dict(cc),search_budget=cb,all20_gates=cg,root_disposition='ZERO_QUALIFIED_SURVIVORS',scientific_summary=csummary,procedure='GET tool yield session omitted then documentary receipt recovery overlapped unfinished timeout; true failed outcome/reaping retained. No universal synchronous/process/body-read PASS.',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=cex)
den['root_r492_scope']=csummary;den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key']});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'0711.3388','10.4086/toc.2011.v007a009','inverse conjecture for the gowers norm is false'})
den['records'].append(dict(url=failure['url'],reason=dict(status=failure['error'],artifact='Lovett-Meshulam-Samorodnitsky Inverse Conjecture for the Gowers Norm is False,0711.3388,ToC7(2011)131-145,DOI10.4086/toc.2011.v007a009',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable; no retry/alternate identity/indirect recovery. Distinct works not blanket denied.'),evidence=dict(path=str(C/'guard-ledger.jsonl'),sha256=sha(C/'guard-ledger.jsonl'))))
delta+=' '+csummary+' NEW entire0711.3388/ToC inverse-Gowers work unavailable after timeout. No retries/alternate deliveries.'
# All assertions above precede integration and preparation mutations.
save(P/'expanded-corpus-r491-parent-integration.json',record)
save(P/'expanded-corpus-r492-parent-integration.json',crecord)
save(P/'pagerank-uniform-source-parent-integration-sol-r1.json',brecord);save(denpath,den)
import shutil
R=P/'pagerank-uniform-primary-qualification-sol-r2';assert not R.exists();R.mkdir();(R/'inputs').mkdir()
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','charge_search.py']:
 shutil.copyfile(B/name,R/name)
shutil.copyfile(denpath,R/'inherited-denials.json')
for q in (B/'inputs').iterdir():
 assert q.is_file() and not q.is_symlink();shutil.copyfile(q,R/'inputs'/q.name)
for name in ['REVIEW.md','PROOF.md','review.json','DORMANT-BRIEF.md','source-map.json','resource-inventory.json']:
 q=B/name
 if q.exists():shutil.copyfile(q,R/'inputs'/('r1-'+name))
save(R/'reservation.json',dict(ids=[316846],rows=[literal],purpose='Focused actual distinct primary PageRank optimization theorem/proof comparison; retain original-final denial and ordinary PASS, no formal dispatch'))
(R/'reservation.sha256').write_text(sha(R/'reservation.json')+'  reservation.json\n')
save(R/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
# Retain the complete tested operational/source boundary; prepend a narrow overriding remit.
oldtask=(B/'TASK.txt').read_text().replace(str(B),str(R)).replace('expanded-corpus-r491 and cubical-zigzag-final-primary-sol-r3','expanded-corpus-r494 and expanded-corpus-r493')
task=f'''FOCUSED R2 OVERRIDE — ONLY GPT-6.1 Sol, high effort, default speed. Personally do the narrow independent actual-primary comparison for MathDB316846. No children/fallback/mathematical programs/formal tools. Current57/60 beyond39,96 total. Root orchestrates; no self credit or formal dispatch.

FIRST shell command EXACTLY:
timeout 20 python3 -I -B {R}/bootstrap.py
SECOND shell command EXACTLY:
timeout 140 python3 -I -B {R}/verify_frozen.py before
No punctuation/chaining. Read all printed TASK/AGENTS. Own inputs/products and explicit PDF skill ONLY; all sibling/ROOT/author lanes/embedded paths protected. Active/planned peers expanded-corpus-r494 and expanded-corpus-r493 entirely protected including stat/hash/list/glob/poll. Every other substantive operation absolute own run.py UNIQUE_LABEL Python stdin with timeout140; writes absolute own write_lane.py. Keep copied operational rules below.

R1 is completed: independent full ordinary/literal PASS INCLUDING source Theorem12 chain-first-node bridge. Read inputs/r1-REVIEW.md, r1-PROOF.md, r1-review.json and exact literal first. Do NOT duplicate the full ordinary proof or treat this as a formal task. R1 reconstructed the proposed mechanism, not independent invention. Header2007/footer2022 source anomaly remains. Actual one-row source Theorem5 tools alone do not provide the multirow fixed-outside-row transposition; sequential legal accessibility and changing-value signs would need proof. Strong positive case: full all-graph/all-damping conjecture, substantive coordinated permutation/external-feedback residual/uniform objective bridge, not a domain or constant correction. Strong contrary case: a precise applicable general PageRank/MDP optimization theorem could fully subsume it; only a complete theorem/proof-to-target reduction establishes that, not standard vocabulary/shortness.

YOUR TASK: authenticate the actual DISTINCT Csaji/general PageRank optimization primary works/theorem bodies/action sets/objectives indicated only as unread navigation. Use observed authoritative primary navigation, no invented identity. Read relevant full theorem/proof and all constraints needed. Compare fixed entire outside-origin rows, fully variable inside-origin simple loop-permitted edges, positive outdegrees, first-exit accessibility, uniform personalization, global discounted argmax and external inlink assertion. Supply either a complete actual published prior-to-target bridge/routine adaptation with all constraints and conclusions, or precise bounded theorem-level nonmatch and substantive residual gap. Exact earlier printed resolution must be backed by body. No complete matching body => no public exclusion. Specific identified unread applicable proof => HOLD. Generic worldwide unknown is not automatic veto; bounded nonmatch is not novelty. State strongest opposing significance cases and recommend adjudication. Do not silently replace the whole source conjecture with generic computation of an optimum.

ORIGINAL/FINAL ABSOLUTELY CLOSED: entire Maximizing PageRank via outlinks, original0711.2867/final LAA429(2008)1254–1276 DOI10.1016/j.laa.2008.01.023 PIIS0024379508000529 returned403. ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect recovery of that work unavailable. No final/correction metadata searches intended to recover it. Provided pre-denial original/thesis only, NOT final equivalence. Distinct optimization primary papers are not blanket denied. Keep original-final HOLD explicitly, even if bounded prior/significance prospectively passes. No Hamming/Brunk-Huczynska recovery. Four registry ROOT artifacts remain closed; no README/tree/API refresh/reconstruction. Read COMPLETE latest inherited-denials before any requests, recover truncations.

R1 used ZERO GETs and ZERO searches; this R2 may use ONLY the unused allowance total max6 guarded GET HOPS including redirects, max2 native SEARCH calls/6 query strings. No budget reset across rounds (R1=0). Sole immutable source_get_guard.py under own runner, one manually chosen persisted plan/invocation, route316846, NEW own destination, observed exact URL, source_identity/purpose>=12 characters. No APIs incl /server/api/, custom transports/HEAD/browser/POST/accounts/TLS/cookie/JS/meta-refresh workarounds. Before each search persist exact query plan through writer, read LIVE counters, precharge immutable absolute charge_search.py under runner, preserve full actual response immediately. No reset/refund/alternate fetch after failure. Failed identified work ALL NEW deliveries closed. Actual guard/access/frozen/counter/cap breach STOP/quarantine preserving evidence. Documentary typo/render/serialization failure is not automatically a breach. No Git/install/publication/external message/tmp/shared/parent writes.

Deliver REVIEW.md and keyed review.json with separate O1 original-final (retained HOLD), O2 actual distinct prior theorem/proof comparison, O3 significance and routine-adaptation objections, family57+39, procedure/acceptance; full bridge or precise GAP, source/visual/read/access/search/resource inventories, all receipts. Conditional updated dormant Sol brief only if scientifically warranted; NO implementation/dispatch. Final standalone verify_frozen.py after, then exhaustive own-file SHA manifest including ALL completed receipts and exact terminal noncircular exclusions, no later frozen writes. Caps: affinity2,childCPU115,supervisor120,AS6GiB,sampledgroupRSS6GiB,deadline130/outer140,arena2. Read-only native own rendered image presentation explicitly allowed, creation/processing under runner, native/transient/writer peaks unknown. Credit0,57/60 unchanged.

FOLLOWING INHERITED R1 OPERATIONAL/SOURCE SPECIFICATION IS COPIED FOR COMPLETE BOUNDARIES. This R2 narrow remit supersedes instructions there to reconstruct the full ordinary proof before reading author proof; those tasks are ALREADY paid and must not be repeated. Existing copied r1 files are read-only reviewed inputs, not new outputs. Protected peers are r494 and r493 as above, regardless historical labels in copied inventories.
\n'''+oldtask
(R/'TASK.txt').write_text(task)
ff=[q for q in R.iterdir() if q.is_file() and q.name!='search-budget.json']+list((R/'inputs').iterdir());save(R/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(R),mathdb_id=316846,task_sha256=sha(R/'TASK.txt'),frozen_bindings=len(ff),model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,credit=0,protected_peers=['expanded-corpus-r494','expanded-corpus-r493'])
save(ROOT/'pagerank-primary-qualification-r2-ready.json',ready);save(ROOT/'selection-routing-pagerank-primary-qualification-r2.json',dict(ids=[316846],sources=[literal['source_url']],lane=str(R),task_sha256=ready['task_sha256'],metadata_only=True))
base=read(ROOT/'r492-config.json');base.update(number=493,protected_peers=['expanded-corpus-r494',R.name],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{491,492}),quarantined_discovery_numbers=[395,463,466,482],denials=str(denpath),peer_routing_files=['selection-routing-r492.json','selection-routing-pagerank-primary-qualification-r2.json'],year_floor=2000,candidate_pool=400)
base['steering']+='\n'+delta+'\n'
save(ROOT/'r493-config.json',base)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);rd=module.prepare(base)
allow493=read(Path(rd['lane'])/'historical-results-allowlist.json')
for name in allow493:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
config494=json.loads(json.dumps(base));config494.update(number=494,protected_peers=['expanded-corpus-r493',R.name],peer_routing_files=['selection-routing-r493.json','selection-routing-pagerank-primary-qualification-r2.json'])
save(ROOT/'r494-config.json',config494);rd494=module.prepare(config494)
assert not set(rd['ids'])&set(rd494['ids'])
save(ROOT/'r491-pagerank-completion-boundary-delta.json',dict(utc=now,message=delta,protected_peers=['expanded-corpus-r492',R.name,'expanded-corpus-r493'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(r491_files=149,r491_bindings=20,r491_frozen=13,pagerank_files=76,pagerank_frozen=27,review_ready=ready,discovery_ready=rd,discovery494_ready=rd494,accepted_new=57,credit=0)))
