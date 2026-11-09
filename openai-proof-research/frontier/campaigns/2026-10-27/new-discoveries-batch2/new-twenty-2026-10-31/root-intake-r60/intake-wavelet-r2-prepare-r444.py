import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
active_peers=['expanded-corpus-r442','expanded-corpus-r443']
A=P/'graph-wavelet-minimax-primary-comparison-sol-r2'
manifest=json.loads((A/'SHA256-MANIFEST.json').read_text());rows=manifest['files']
assert len({x['path'] for x in rows})==len(rows)
for row in rows:
 q=A/row['path'];assert q.is_relative_to(A) and not q.is_symlink()
 assert sha(q)==row['sha256'] and q.stat().st_size==row['bytes'],str(q)
excluded=json.loads((A/'TERMINAL-EXCLUSIONS.json').read_text())['exact_self_exclusions']
actual={str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}
assert actual=={x['path'] for x in rows}|set(excluded)
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==170
for n,h in f.items():
 q=Path(n)
 assert not any(q.is_relative_to(P/x) for x in active_peers)
 assert sha(q)==h,n
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==170 and after['mismatches']==[]
rec=[]
for row in rows:
 if row['path'].endswith('.receipt.json'):
  q=A/row['path'];v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  rec.append(dict(path=row['path'],sha256=sha(q),exit=v['exit']))
terminal=A/'terminal_manifest_20.receipt.json';t=json.loads(terminal.read_text());assert t['exit']==0
rec.append(dict(path=terminal.name,sha256=sha(terminal),exit=t['exit']))
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()]
counts=collections.Counter(x['event'] for x in events)
assert counts==dict(attempt=5,success=3,redirect=1,unavailable=1)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
finding=json.loads((A/'keyedreview.json').read_text())['332073'];assert finding['O1']['status']=='HOLD' and finding['O3']['status']=='HOLD' and finding['formal_dispatch']==False
den=json.loads((ROOT/'inherited-denials-r442.json').read_text());den['utc']=now
failure=next(e for e in events if e['event']=='unavailable');assert failure['status']==202
doi='https://doi.org/10.1184/R1/12026448.V1'
keys={urlsplit(u).hostname.lower()+unquote(urlsplit(u).path).rstrip('/') for u in [doi,failure['url']]}
den['blocked_keys']=sorted(set(den['blocked_keys'])|keys)
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1184/r1/12026448.v1','10.1184/r1/12026448','exploiting structure in data: sampling and signal processing on graphs'})
restriction='Entire identified thesis artifact unavailable: ALL new alternate host/query/version/PDF/API/cache/mirror/author/DOI deliveries blocked after institutional HTTP202. Saved pre-failure mirror is navigation only, not authenticated primary author/date identity or chapter proof; no later indirect recovery. Original1512.05406v1 is a distinct already-cached work, not thesis coverage.'
den['records'].append(dict(url=failure['url'],reason=dict(status=202,artifact='Exploiting Structure In Data: Sampling and Signal Processing on Graphs, DOI10.1184/R1/12026448.V1',restriction=restriction),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
den['root_wavelet332073_thesis_scope']=restriction+' O1/O3 HOLD. Official Chen CV authenticates planned submission only; bounded author publication-list and searches identify no final, not universal absence. Ordinary/v1 PASS retained; no complete routine exclusion established, no formal routing/credit. R1 missing full search response remains historical procedureFAIL; no backfill/counter reset.'
denpath=ROOT/'inherited-denials-r444.json';save(denpath,den)
report=dict(utc=now,mathdb_id=332073,review_lane=str(A),review_sha256=sha(A/'REVIEW.md'),manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=len(rows),verified_frozen_bindings=len(f),runner_receipts=rec,runner_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),guard_events=dict(counts),search_budget=budget,root_disposition='PARKED_SPECIFIC_PRIMARY_THESIS_UNAVAILABLE',ordinary_original_v1='retained independent PASS',O1='HOLD unauthenticated primary thesis identity and unread applicable Chapter4 Algorithm6/Theorems28-29 proofs',O2='bounded investigation PASS; planned submission only, no final identified, no worldwide negative',O3='HOLD specific thesis comparison; no complete routine exclusion adopted',significance='unqualified pending specific applicable primary body; no inference from smallness/standard tools alone',process='r2 disclosed local tool failures and prospective bounded capture; r1 full search response omission remains FAIL, not repaired',root_scope='Documentary metadata/integrity intake only; no mathematical programs/compiler/checker or new proof validation at root',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,latest_denials=str(denpath),protected_active_peers=active_peers,terminal_self_exclusions=excluded,terminal_receipt_sha256=sha(terminal))
save(P/'graph-wavelet-minimax-primary-parent-integration-sol-r2.json',report)

# Reuse only the complete metadata preparation tail, not the earlier intake mutations.
base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text()
tail=base_source[base_source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
peer_ids={326555,324571,332073};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406'}
for n in [442,443]:
 meta=json.loads((ROOT/f'selection-routing-r{n}.json').read_text())
 peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
L=P/'expanded-corpus-r444';assert not L.exists()
tail=tail.replace('selection-routing-r434.json','selection-routing-r444.json').replace('for num in range(421,434):','for num in range(421,442):')
tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active_peers))
tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60')
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2']:")
tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root separated this20 from all forty retained sibling IDs and all sibling source URLs using root-owned immutable routing metadata; no sibling reservation access. Also exclude accepted57 and held332073.')
steering='''
LATEST ROOT ROUTING authoritative:57/60 accepted beyond39 prior,96total. ONLYGPT-6.1Sol high/default ALLagents, nochildren/fallback. Root orchestrates/documentary metadata only. Accepted#56shoe324571full countable-law uniform supremum<=255/256<1 and#57CMDRR326555universal nonexistence passed full independent literal/final-source/body/kernel/dependency-audit/source-only-replay/paper review. Root acceptance retains bounded prior-access and historical process qualifications, not worldwide novelty or blanket historical compliance. Stale55/60zero-credit author handbacks are historical. No helpers/finite-countable/constant/row-column variants counted again.
ACTIVE expanded-corpus-r442 and expanded-corpus-r443 FULLYPROTECTED: no read/hash/glob/list/stat/poll evenmetadata/reservation/status. Root has excluded all40 IDs and all primarysourceURLs from retained routing metadata. All other formal/code-loop/Polynexus/crown/tournament/bunkbed/Hat bodies remain protected. Oldr395 all76acquisitions permanently quarantined.
Completed wavelet332073 focused r2: ordinary/original1512.05406v1 PASS strict support4>2 with FULL competing orthonormal basis INCLUDING globalmean; no mean-zero surrogate. Specific successor thesis Exploiting Structure In Data: Sampling and Signal Processing on Graphs DOI10.1184/R1/12026448.V1 redirected to CMU12026448/1 and returnedHTTP202: ENTIRE thesis all alternate host/query/version/PDF/API/cache/mirror/author/DOI deliveries NOWUNAVAILABLE. No retry/indirect recovery. Mirror's RohanVarma/May2020 identity unauthenticated; actualprimary Chapter4Algorithm6/Theorems28-29 proofs/credit/bibliography UNREAD. O1/O3HOLD, no routine exclusion adopted/no formal dispatch/credit. Official Chen CV authenticates planned submission only; bounded authorpublicationlist/searches identify no final, not universal negative. Original-v1 source unequal-community intuition is not a complete minimax bridge; standardtools/smallwitness alone insufficient exclusion. R1 missing full search response persists procedureFAIL, no historical backfill/counter reset. CurrentMathDB332073 record challenge remains unavailable. Original cached work is distinct from thesis, no thesis coverage from it.
Completedr440all0:350044fullordinary tripartite forest-bound proposal PARKED actual finalJGT10.1002/jgt.22812/original2103.05294Wiley403 ALLnewalternatebodydelivery unavailable, cachedoriginal NOTfinalequivalence; exactMathDB350044challenge-suffix unavailable. No formal/newretrieval lane.328499/325707actualAshrafProp11public onefamily zero.329239 weightedtableau/skewADS gap;329238generalHL-tbranching gap;328767Snrow-sum/degree/zero-one-summand gap. Completedr441all0:323877ownsourcev2 formula12atn3vswalkcount8 sourcecorrection zero;324271globaltreeordering leafpathrerouting gap,332117quotientgeneration only not exactPreRGB/POT/sameblock/BezoutC4 scope; other16primarybodies unread.
Earlier327053lattice ordinaryproposal PARKED finalJNT10.1016/j.jnt.2014.02.015/1401.2891denied, exactMathDB327053/332073challenge unavailable.332892Z6MAXgamma sumsetproposal PARKED finalMathematika10.1112/S0025579315000157/1307.8396denied.341052rounding ordinary/probability PASS but exactYe1999DOI10.1007/s10107980012a blockedHTTPredirect/allalternate delivery denied; final/significance unpaid. All inherited denial scope binding. No HTTPupgrade/TLS/cookie/alternate-host/query/version/cache/mirror/API/author/DOI workaround; no old ledger edits/backfill.
Readactual primary definitions and stronger existing theorem/proof/ownexample before major investment. Source-own/publicsolutions/complete routine bridges/wording-domain-endpoint corrections ZERO. No exclusion merely for shortness, standard tools or smallness. Specific applicable unread body preciseHOLD; generic worldwideunknown not automatic veto; bounded nonmatch not worldwide novelty. ExactIDkeys/sourcefields in history, never hash-digit matches/neighbor-disposition transfer. Root intake only integrity/routing, not new mathematical clearance.
'''
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r444','exec'),ns)
rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids
assert not {x.get('source_url') for x in rr['rows']}&peer_sources
task=(L/'TASK.txt').read_text();assert 'Resources fixed:' in task and 'wholelane maximum3 actual calls9' in task and 'HTTP202' in task
frozen=json.loads((L/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(n))==v for n,v in frozen.items())
assert not (L/'bootstrap-receipt.json').exists()
save(ROOT/'r444-ready.json',dict(utc=now,accepted_new=57,target_new=60,completed_intake=report,lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],latest_denials=str(denpath),active_peers=active_peers,model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,review_manifest_files=len(rows),frozen_bindings=len(f),receipt_exit_counts=report['runner_exit_counts'],ready_lane=str(L),ids=rr['ids'],task_sha256=sha(L/'TASK.txt'))))
