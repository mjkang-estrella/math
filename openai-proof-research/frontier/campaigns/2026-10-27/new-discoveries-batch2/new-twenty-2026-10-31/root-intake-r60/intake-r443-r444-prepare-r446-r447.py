import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
reports=[]
for number in [443,444]:
 A=P/f'expanded-corpus-r{number}';m=json.loads((A/'MANIFEST.json').read_text());rawfiles=m['files']
 mf={v['path']:v for v in rawfiles} if isinstance(rawfiles,list) else rawfiles
 assert len(mf)==(145 if number==443 else 68)
 for n,v in mf.items():
  q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],str(q)
 exclusions=m['terminal_noncircular_self_exclusions' if number==443 else 'self_exclusions']
 assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
 f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==12 and all(sha(Path(n))==v for n,v in f.items())
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
 reservation=json.loads((A/'reservation.json').read_text());ids=set(reservation['ids']);gates=json.loads((A/'results.json').read_text());assert len(ids)==20 and ids==set(map(int,gates))
 prov=json.loads((A/('literal-provenance.json' if number==443 else 'original-provenance.json')).read_text())
 prows=[(str(v['id']),v) for v in prov] if isinstance(prov,list) else list(prov.items());assert set(map(int,(k for k,v in prows)))==ids
 chunks={};bindings=[];rawparts=[]
 for key,row in prows:
  q=Path(row['chunk' if number==443 else 'chunk_path']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];assert h==row['chunk_sha256'];line=row['line' if number==443 else 'one_based_line'];raw=lines[line-1]
  assert dg(raw)==row['raw_sha256' if number==443 else 'raw_line_including_newline_sha256']
  if number==443:assert raw==base64.b64decode(row['raw_line_base64']) and row['newline'] and raw.endswith(b'\n') and json.loads(raw)==row['object']
  else:assert (A/f'originals/{key}.jsonl').read_bytes()==raw and raw.endswith(bytes.fromhex(row['newline_hex']))
  obj=json.loads(raw);assert obj['mathdb_id']==int(key)
  token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
  assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256']
  statement=json.loads(token);assert statement==obj['statement']==gates[key]['statement']
  assert dg(statement.encode())==row['decoded_statement_sha256' if number==443 else 'decoded_statement_utf8_sha256']
  bindings.append(int(key));rawparts.append((str(q),line,raw))
 if number==443:assert (A/'original-literals.jsonl').read_bytes()==b''.join(v[2] for v in sorted(rawparts))
 receipts=[]
 for q in sorted(A.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
 budget=json.loads((A/'search-budget.json').read_text())
 if number==443:
  events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=13,success=12,redirect=1)
  for e in events:
   if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
  assert budget['calls_precharged']==3 and budget['querystrings_precharged']==9
  for k in [1,2,3]:json.loads((A/f'search{k}-response.json').read_text())
  failure=json.loads((A/'process-qualification.json').read_text());assert failure['status']=='FAIL'
  process='FAIL retained: exact source-URL/scalar-ID history reconciliation completed late after investment; eight same-source neighbor histories later reconciled, no neighbor disposition transfer. No acceptance eligibility.'
  summary='345467 full literal-v3 counterexample is direct parameter/endpoint perturbation of source own sharpness example; recommend exclusion, no prior printed exact counterexample claim.345465 and351824 source-own solved.325281 six-barrier/odd-cycle augmentation and345466 longest-cycle charging gaps;356239 bounded/unbounded-color converse gap. Seven reserved IDs selected primary passages read, thirteen bodies unread.'
 else:
  assert not (A/'guard-ledger.jsonl').exists();counts=collections.Counter();assert budget['calls_used']==0 and budget['queries_used']==0
  failure=json.loads((A/'PROCEDURE-FAIL.json').read_text());assert failure['status']=='FAIL_QUARANTINE_NETWORK_STOP'
  process='Worker FAIL/network-stop retained: second command had extra inert positional dot, verifier exit0/all12 intact. Root dispatch itself placed punctuation beside exact command, an avoidable ambiguity; preserve both, no historical rewrite or scientific qualification. This is command-fidelity deviation, not evidence of source/frozen/access compromise. All20 primary/current-prior checks remain unpaid.'
  summary='All20 literal reviews only. Kneser-treewidth lower bound, total1-2-coloring global Boolean feasibility, and activity recursion/splitting remain gaps.339714/324630/325802 literal-definition/endpoint observations unqualified zero credit. No HTTP/search/current registries/primary-body review, no denial invented.'
  assert failure['get_hops']==0 and failure['search_calls']==0
 report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=len(mf),verified_original_bindings=sorted(bindings),verified_frozen_bindings=12,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(v['exit']) for v in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_PROCESS_FAIL_RETAINED',scientific_summary=summary,process=process,all20_gates={k:{'mathdb_id':v['mathdb_id'],'source_url':v['source_url'],'disposition':v['disposition'],'gates':v['gates'],'credit':v['credit']} for k,v in gates.items()},root_scope='Integrity/provenance/documentary routing only, no root mathematical solving/programs/Lean/checker execution',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions,root_reader_note='Initial bounded schema reader wrongly used dict.values on list provenance; AttributeError before any mutation. Recovered via explicit schema-specific readers; not a proof or worker failure.')
 save(P/f'expanded-corpus-r{number}-parent-integration.json',report);reports.append(report)

den=json.loads((ROOT/'inherited-denials-r445.json').read_text());den['utc']=now
# The saved purported final is only auto-redirect HTML, not an article body. Keep transport history intact.
A=P/'expanded-corpus-r443';nav=A/'sources/paths-final.html';b=nav.read_bytes();assert len(b)==2695 and b'<title>Redirecting</title>' in b and b'HTTP-EQUIV="REFRESH"' in b
urls=['https://doi.org/10.1016/j.jctb.2020.08.003','https://linkinghub.elsevier.com/retrieve/pii/S0095895620300782']
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(u).hostname.lower()+unquote(urlsplit(u).path).rstrip('/') for u in urls})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1016/j.jctb.2020.08.003','s0095895620300782','2002.04198','a strengthening of erdos-gallai theorem and proof of woodall conjecture'})
restriction='Identified JCTB2021 final DOI10.1016/j.jctb.2020.08.003/PII S0095895620300782/source2002.04198: purported final payload is2695-byte redirect-only HTML with meta-refresh/JS, no article body. Root manual classification entire work unavailable for ALLnew alternate host/query/version/cache/mirror/API/author/DOI/body deliveries; no script/cookie/redirect bypass. Already-cached v3 only where expressly copied, not final equivalence. Old guard transport200 success row preserved, no backfill.'
den['records'].append(dict(url=urls[1],reason=dict(status='transport200 redirect-only HTML; root manual unavailable classification',artifact='Li-Ning strengthening Erdos-Gallai/Woodall JCTB2021 final',restriction=restriction),evidence=dict(path=str(nav),sha256=sha(nav),guard_ledger=str(A/'guard-ledger.jsonl'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
den['root_r443_r444_scope']=restriction+' r443 all0/processFAILlatehistory; r444 all0/extra-dot command fidelity failure with root punctuation ambiguity, zero network and allprimarybodies unread; no mathematical taint or source qualification inferred from metadata.'
denpath=ROOT/'inherited-denials-r446.json';save(denpath,den)

base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();base_tail=base_source[base_source.index('# Metadata selector:'):];base_tail=base_tail[:base_tail.rfind('\nprint(')]
tree=ast.parse((ROOT/'intake-wavelet-r2-prepare-r444.py').read_text());steering0=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
peer_ids={326555,324571,332073};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406'}
meta=json.loads((ROOT/'selection-routing-r445.json').read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
ready=[]
for number,other in [(446,447),(447,446)]:
 L=P/f'expanded-corpus-r{number}';assert not L.exists();active=['expanded-corpus-r445',f'expanded-corpus-r{other}']
 tail=base_tail.replace('selection-routing-r434.json',f'selection-routing-r{number}.json').replace('for num in range(421,434):','for num in range(421,445):')
 tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active))
 tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
 tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60')
 tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2']:")
 tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded retained sibling IDs/sourceURLs using root-owned routing metadata; no active-child file access. Accepted57 and held332073 also excluded.')
 tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes')\ntask=core+latest")
 steering=steering0.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443',f'ACTIVE expanded-corpus-r445 and expanded-corpus-r{other}')
 steering+='\nCompletedr442all0:330282 and356879actualpublic-source refutations;356624uniformdeBruijnlengthlift,342128arbitrarymatroidrankbound,381465exactnonabelianEGZ unpaid. Completedr443all0,processFAILlate exactsourcehistoryreconciliation retained/noacceptance.345467literalv3 sixvertexcounterexample direct endpointperturbation of source own example,complete bridge/contrarycase documented,zero significantcredit.345465/351824sourceownsolved;325281sixbarrier/oddcycleintegrality and345466cyclecharging gaps,356239unboundedcolorconverse unpaid. IdentifiedLi-NingJCTB2021final10.1016/j.jctb.2020.08.003/PIIS0095895620300782/2002.04198 nowALLnewbodydelivery unavailable:root personally inspected2695byteRedirecting meta-refresh/JS only. Noalternate host/query/version/cache/mirror/API/author/DOI/body/script/cookie bypass. Cachedoriginalv3 onlywhereexplicitcopied,no final equivalence. Guardtransport200history unchanged,rootmanual classification separate. Completedr444all0:all20primary/currentregistrybodies unread,zeroGET/search after extra positionaldot in verifiercommand. Root dispatch punctuation ambiguous; workerFAIL retained,all12frozen intact. Kneserlowerbound/globaltotal1-2labeling/activityrecursion gaps; literal-wording/endpoint observations zero. Noacceptance/formaldispatch.\n'
 steering+='\nCOMMAND CLARITY: execute first two own-lane commands exactly as the standalone TASK lines; no trailing dot or prose punctuation. An inert extra argument to an own verifier that nevertheless exits0and verifies all12 under the required caps is a recorded invocation-fidelity deviation, not an external-source policy breach or automatic reason to abandon all remaining research. Preserve failures/deviations and correct prospective commands; do not rewrite old evidence or rerun successful bootstrap. Genuine unauthorized protected/frozen access, cap violations, source-guard/network/budget violations retain task stop/disclosure rules. Before source investment complete BOTH exactID/scalarID and exact sourceURL structural history reconciliation, no neighbor-disposition transfer.\n'
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
 ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{number}','exec'),ns)
 rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
 peer_ids.update(rr['ids']);peer_sources.update(x.get('source_url') for x in rr['rows'])
 task=(L/'TASK.txt').read_text();assert 'Current55/60' not in task and 'wholelane maximum3 actual calls9' in task and 'COMMAND CLARITY' in task
 fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==12 and all(sha(Path(n))==v for n,v in fb.items()) and not (L/'bootstrap-receipt.json').exists()
 ready.append(dict(lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],role='research'))
save(ROOT/'r446-r447-ready.json',dict(utc=now,accepted_new=57,target_new=60,completed_intakes=[str(P/f'expanded-corpus-r{n}-parent-integration.json') for n in [443,444]],packets=ready,latest_denials=str(denpath),model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,intakes=[dict(lane=x['source_lane'],manifest_files=x['verified_manifest_files'],original_bindings=len(x['verified_original_bindings']),frozen_bindings=x['verified_frozen_bindings'],receipt_exit_counts=x['receipt_exit_counts']) for x in reports],packets=ready)))
