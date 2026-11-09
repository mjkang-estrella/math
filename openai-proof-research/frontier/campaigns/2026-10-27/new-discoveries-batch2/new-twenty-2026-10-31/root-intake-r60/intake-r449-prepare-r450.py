import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil,base64,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
A=P/'expanded-corpus-r449';m=json.loads((A/'manifest.json').read_text());mf=m['files'];assert len(mf)==92
for n,v in mf.items():
 q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_non_circular_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==13 and all(sha(Path(n))==v for n,v in f.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
rr=json.loads((A/'reservation.json').read_text());gates=json.loads((A/'results.json').read_text());assert len(rr['ids'])==20 and set(rr['ids'])==set(map(int,gates))
prov=json.loads((A/'originals.json').read_text());assert set(map(int,prov))==set(rr['ids']);chunks={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert raw==base64.b64decode(row['raw_base64']) and dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n')
 obj=json.loads(raw);assert obj==row['object'] and obj['mathdb_id']==int(key)
 for field,pkey in [('statement','statement_provenance'),('statement_completeness','statement_completeness_provenance')]:
  token=re.search(rb'"'+field.encode()+rb'"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1];v=row[pkey]
  assert token.decode()==v['raw_token'] and dg(token)==v['raw_token_sha256'] and json.loads(token)==obj[field] and dg(obj[field].encode())==v['decoded_utf8_sha256']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(v['event'] for v in events);assert counts==dict(attempt=5,success=5)
for v in events:
 if v['event']=='success':assert sha(A/v['destination'])==v['sha256']
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256']
 plan=json.loads((A/c['plan']).read_text());assert plan['queries']==c['queries']
 expected=dict(prev);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected
 json.loads((A/f'search-response-{i}.json').read_text());prev=expected
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=92,verified_original_bindings=sorted(rr['ids']),verified_frozen_bindings=13,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Both precharge old/new states, plan digests, querystrings, final live budget and full saved responses independently checked; immutable helper unchanged',root_disposition='ZERO_QUALIFIED_SURVIVORS',public_result_exclusions=[352639,344760,376136],endpoint_correction=338284,scientific_summary='352639 actualKeusch2303.02611v4T1 public1-2-3 theorem;344760 actualsource-own field-automorphism/convex-halfplane similar-copy refutation;376136 actual2607.18031v1T1.2 and stronger matrix theorem source-own. Authored complete bridges retained, not root independent theorem audits.338284K1/P4 full literal counterexample only single-vertex factor endpoint, zero; nontrivial product unchanged.346690 requires ONE coloring/all s,k and fixed h; fixed-k theorem/compactness and two failed multiplicative trials do not pay uniform one-sided bound. Fifteen reserved primary bodies unread.',all20_gates={k:{a:b for a,b in v.items() if a!='literal'} for k,v in gates.items()},process='Receipted work with true limits; no new denial/procedure breach reported. Native/writer telemetry and transients unavailable. Root bounded reader displayed large external binding map and truncated output; this was metadata only, no embedded paths followed; relevant scalar fields recovered separately.',external_manifest_bindings='760 reported prior corpus/history/instruction hashes are retained documentary evidence, not followed or freshly re-audited by root. Root independently verified own92files, all20 corpus raw/token/decoded/completeness bindings and frozen13 only.',root_scope='Metadata/provenance/integrity/routing only; no mathematical solving/program/compiler/checker execution',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r449-parent-integration.json',report)
den=json.loads((ROOT/'inherited-denials-r448.json').read_text());den['utc']=now;den['root_r449_scope']='All0:352639/344760/376136authenticated public/source-own results;338284singlevertexfactorboundarycorrection0;346690uniformcoloringgap.92ownmanifestfiles/20raw-token-decoded-completenessbindings/13frozenverified.5GETsuccess,no newdenial;2search6queries with authenticatedliveprechargecontinuity. Four inheritedregistryroot504artifacts notrefetched; no currentheads/proofclearance inferred.'
denpath=ROOT/'inherited-denials-r450.json';save(denpath,den)

base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=base_source[base_source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
active=['expanded-corpus-r448','tree-hom-hitting-source-review-sol-r1'];peer_ids={326555,324571,332073,351988};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406','https://arxiv.org/abs/2109.09249'}
meta=json.loads((ROOT/'selection-routing-r448.json').read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
L=P/'expanded-corpus-r450';assert not L.exists()
tail=tail.replace('selection-routing-r434.json','selection-routing-r450.json').replace('for num in range(421,434):','for num in [n for n in range(421,450) if n != 448]:')
tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active))
tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60').replace("'frozen_bindings':12","'frozen_bindings':13")
tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded all retained r448 IDs/sourceURLs and reviewer351988/2109.09249 using root-owned metadata only; accepted57 excluded.')
tail=tail.replace("shutil.copyfile(denpath,L/'inherited-denials.json')","shutil.copyfile(ROOT/'charge_search.py',L/'charge_search.py')\nshutil.copyfile(denpath,L/'inherited-denials.json')")
tail=tail.replace("'historical-results-allowlist.json','TASK.txt']","'historical-results-allowlist.json','TASK.txt','charge_search.py']")
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2']:")
tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes').replace('Twelve immutable frozen bindings','Thirteen immutable frozen bindings')\ntask=core+latest")
tree=ast.parse((ROOT/'intake-wavelet-r2-prepare-r444.py').read_text());steering=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
steering=steering.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443','ACTIVE expanded-corpus-r448 and tree-hom-hitting-source-review-sol-r1')
steering+='\nActive351988independent full ordinary Gaussian-kernel/determinant/forest/Wiener/hittingtime/source/prior/significance/family review, NOformal. Final351988DAM389(2026)119-125DOI10.1016/j.dam.2026.03.043/PIIS0166218X26001903/source2109.09249 andSidorenko1994DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 denied403 ALLnewbodydeliveryunavailable,onlycachedv4explicitcopiesnotfinalequivalence. Four exactregistryrootmetadataartifacts504 unavailable; NOroot/README/tree/API/branch/versionalternate refresh/retry, notblanketban oneverydistinctproofpublication/GitHubrepo. Datedcachedheads navigationonly, no currentproof/chronology/noveltyclearance or worldwideabsence. Actual independentlyidentifiedconcretecounterclaimbodyneeded, specificunreadHOLD/genericunknownnotautomaticveto. LiNingJCTB2021DOI10.1016/j.jctb.2020.08.003/2002.04198redirect-onlyHTML ALLnewdeliveryunavailable. Allpreviousdenialsbinding.\n'
steering+='\nCompletedr442public330282/356879zero,gapsdeBruijnlength/matroidrank/exactnonabelianEGZ. r443345467directsourceexampleendpointperturbationzero,345465/351824sourceown,processFAILlatehistory;matching/circumference/unboundedcolorsgaps. r444allprimary/currentregistryunread,zero network after inert verifierdotcommanddeviation with rootpunctuationambiguity,failretained/noacceptance. r445351988reviewonly,pancake350146/weight354432 gaps. r446335867sourceownT3.6/336931definitioncorrectionzero;polymatroid/occupancy/Kempegaps;counter-continuityFAIL,no actualovercapinferred. r447conditional8side347983notrequired6side,labels/staircasesgaps,late-registryFAILretained. r449public352639actualKeuschT1,344760sourceownautomorphism/halfplane fullsimilarityrefutation,376136sourceown stronger matrix/squareenergytheorem allzero.338284K1/P4boundaryzero,nontrivialproductunpaid.346690ONEcoloringALLs,k fixedh notpaidbyfixedkbound/compactness/twofailedmultiplicativeexamples.5GETsuccess/no newdenial;2search6queries livecountercontinuityauthenticated. All20originalstoken/decoded/completeness/13frozen verified;15primarybodiesunread. Rootintakesintegrityonlynotindependentmathproof.\n'
steering+='\nBOOKKEEPING: charge_search.py additional IMMUTABLE frozen helper, THIRTEEN bindings total. Before EACHnativeSEARCH persist exactplan with top-level queries list, invoke ABSOLUTEcharge_search.py ownplanpath UNDERrun.py; helper authenticates liveoldcounters/chargeledger before changing, rejectsduplicate/exhaustion, writesviaownwriter. NEVERdirectlyreplace/editsearch-budget or chargeledger. Afterprecharge exactnativecallONCE, FULLactualresponsesavedIMMEDIATELY beforeotherwork. Wholelane3calls9queries, failedattemptsstaycharged,no refund/reset/backfill. HelperNONnetwork;GETsolefixedguard. Before significant investment reconcile exactIDkeys/scalarIDs AND exactsourceURLmatches, actualrelevantdispositionsread, noneighbortransfer. Sourceown/publicstrongertheorem readbeforeclaimingnew. FirsttwocommandsstandaloneexactTASKlines,no dot/prosepunctuation; inertownverifierargumentwithtrue0/all13checked undercaps documentedinvocationdeviation, notautomaticexternalpolicybreach/abandonment. Seriousaccess/protected/frozen/cap/network/budgetviolationsretainSTOP/disclosure.\n'
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r450','exec'),ns)
rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==13 and all(sha(Path(n))==h for n,h in fb.items()) and not (L/'bootstrap-receipt.json').exists()
ready=dict(utc=now,lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],frozen=13,model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,target_new=60,latest_denials=str(denpath),credit=0)
save(ROOT/'r450-ready.json',ready)
print(json.dumps(dict(accepted_new=57,manifest_files=92,original_bindings=20,frozen_bindings=13,receipt_exit_counts=report['receipt_exit_counts'],search_counter_continuity='verified',ready=ready)))
