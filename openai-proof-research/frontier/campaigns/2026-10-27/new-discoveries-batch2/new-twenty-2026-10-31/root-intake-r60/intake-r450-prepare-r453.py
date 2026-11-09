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
A=P/'expanded-corpus-r450';m=json.loads((A/'manifest.json').read_text());mf=m['own_completed_files'];assert isinstance(mf,dict) and len(mf)==121
for n,h in mf.items():
 q=A/n;assert q.is_relative_to(A) and not q.is_symlink();assert sha(q)==h,n
exclusions=m['terminal_noncircular_self_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(mf)|set(exclusions)
f=json.loads((A/'frozen-inputs.json').read_text());assert len(f)==13 and all(sha(Path(n))==h for n,h in f.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
rr=json.loads((A/'reservation.json').read_text());gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'originals.json').read_text());assert len(rr['ids'])==20 and set(rr['ids'])==set(map(int,gates))==set(map(int,prov));chunks={};rawparts=[]
for key,row in prov.items():
 q=Path(row['path']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert raw==base64.b64decode(row['raw_base64']) and dg(raw)==row['raw_sha256'] and row['newline'] and raw.endswith(b'\n')
 obj=json.loads(raw);assert obj==row['object'] and obj['mathdb_id']==int(key)
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement'] and dg(obj['statement'].encode())==row['statement_utf8_sha256'];rawparts.append(raw)
assert collections.Counter((A/'original20.jsonl').read_bytes().splitlines(keepends=True))==collections.Counter(rawparts)
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'manifest-final.receipt.json').read_text())['exit']==0
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=7)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==2 and budget['queries_used']==6
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'];assert json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(prev);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert expected==c['after'];prev=expected
 json.loads((A/f'search-response{i}.json').read_text())
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
report=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=121,verified_original_bindings=sorted(rr['ids']),verified_frozen_bindings=13,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Plan hashes/querystrings and all live before/after states authenticated to final budget; helper unchanged; both saved full responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS',source_own_exclusion=340211,specific_prior_hold=337615,scientific_summary='340211 actual1808.09167v4Theorem4.4 c3/averaging gives stronger weakDirac source-own result,zero.337615actual1711.02848signedpalette definition and implication proof read; specific Kardos-Narboni2019 counterexample proof/figures unread,not certified by snippets.340492needs one graph simultaneously universal-list-arborable/common-palette-balanced/bad-balanced-list: padding/forcing mechanisms incomplete, corrected K3,N analysis retained.333550two-row button cuts lack uniform remainder/global schedule invariant.339730/339731maximum-label/top-block subfamilies do not prove full bipartite/multipartite classifications;2026actuallaterarticle still conjectures. No full ordinary survivor.',all20_gates=gates,process='Receipted bounded work with explicit mathematical corrections and access/read-depth limits. No new denial, helper/frozen/budget violation reported. Sampled/native/writer limits retained; no universal compliance assertion.',external_manifest_bindings='Reported external corpus/history hashes retained as documentary inventory, not recursively traversed or freshly re-audited; root separately verified own121files, original20bindings, frozen13.',root_scope='Documentary integrity/provenance/routing only; root did not solve or run mathematical programs/Lean/checkers',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r450-parent-integration.json',report)
den=json.loads((ROOT/'inherited-denials-r451.json').read_text());den['utc']=now;den['root_r450_scope']='All0;340211actualsourceownstrongerweakDiracTheorem4.4,337615specificKardosNarboni2019proofbodyHOLD.340492equitablelistarborability/333550two-rowbuttonschedule/339730339731supergracefulclassification gaps.7GETsuccess,no newdenial;2search6queries with authenticatedcountercontinuity.121ownmanifest/20raw-token-decodedbindings/13frozenverified. Earlier scientificPARKS/denials unchanged.'
denpath=ROOT/'inherited-denials-r453.json';save(denpath,den)

base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=base_source[base_source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
active=['expanded-corpus-r451','expanded-corpus-r452'];peer_ids={326555,324571,332073,351988};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406','https://arxiv.org/abs/2109.09249'}
for n in [451,452]:
 meta=json.loads((ROOT/f'selection-routing-r{n}.json').read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
L=P/'expanded-corpus-r453';assert not L.exists()
tail=tail.replace('selection-routing-r434.json','selection-routing-r453.json').replace('for num in range(421,434):','for num in range(421,451):')
tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr(active))
tail=tail.replace("peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}",'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60').replace("'frozen_bindings':12","'frozen_bindings':13")
tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded all forty retained active sibling IDs/sourceURLs using root-owned routing only, no active file access; accepted57 and parked351988 excluded.')
tail=tail.replace("shutil.copyfile(denpath,L/'inherited-denials.json')","shutil.copyfile(ROOT/'charge_search.py',L/'charge_search.py')\nshutil.copyfile(denpath,L/'inherited-denials.json')")
tail=tail.replace("'historical-results-allowlist.json','TASK.txt']","'historical-results-allowlist.json','TASK.txt','charge_search.py']")
tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2','tree-hom-hitting-source-review-sol-r1']:")
tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.','Current57/60 beyond39 prior,96total.').replace('Current accepted55 includes','Current accepted57 includes').replace('Twelve immutable frozen bindings','Thirteen immutable frozen bindings')\ntask=core+latest")
tree=ast.parse((ROOT/'intake-wavelet-r2-prepare-r444.py').read_text());steering=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steering' for t in n.targets))
steering=steering.replace('ACTIVE expanded-corpus-r442 and expanded-corpus-r443','ACTIVE expanded-corpus-r451 and expanded-corpus-r452')
steering+='\nCompleted351988independentreview ORDINARYPASS all source-definedn>=2/explicitabsorbing-singleton convention/emptymeanundefined. V4sourceproofs+Figure4read,actual2014EJCP4.9extremalityprimary boundednonmatch:targetspecificmaxcount/minW not arbitrarypairorder.57+39familyboundednonoverlap. SCIENTIFICPARKfinalDAM3892026DOI10.1016/j.dam.2026.03.043/source2109.09249/PIIS0166218X26001903 andapplicableSidorenko1994DOI10.1016/0012-365X(94)90388-3/PII0012365X94903883 denied403 ALLnewbodydeliveryunavailable,nonewretrieval/formallane/credit. Four exactpublicregistryROOTmetadataartifacts504unavailable:NOroot/README/tree/API/branch/versionalternate refresh/retry/reconstruction; notblanketban everydistinctproofpublication/repo, cannotindirectlyrebuilddeniedmetadata. Datedcachedheads navigationonly, no currentproof/chronology/noveltyclearance/worldwideabsence. Independentlyidentifiedconcretecounterclaim needsactualbody or preciseHOLD;genericworldwideunknownnotautomaticveto. Neighborhood354612final10.1002/jgt.23014/source2205.06464denied403 ALLnewbodydeliveryunavailable;cachedoriginalnotfinalequivalence,proper-coloroctahedron source-domain correction0. DistinctBickle3539742203.10239/2023finalpublicrefutation0. LiNingJCTB2021redirect-only/CMUthesis202/allolddenialsremainbinding.\n'
steering+='\nRecentcompletedall0:r448350680(c)publicTheorem6.13/companionproof,(b)Hankelpositivityunpaid;356877concrete2601.17624exactproofclaim90pagecentralproof/rankreductionunread. r449352639Keusch/344760sourceautomorphismhalfplane/376136matrixsquareenergypublic0;338284singlevertexfactorboundary0,nontrivialproductgap;346690ONEcoloringALLs,k fixedhgap. r450340211actualsourceownstrongerweakDiracT4.4,337615specificKardosNarboni2019proofbodyunreadHOLD;340492universal-list/commonpalette-balanced/badlist simultaneouslyunpaid(correctedK3,Ncase retained),333550boundedremainderlegalschedule two-rowbuttons gap,339730/339731supergracefulglobalclassification gap,later2026article stillconjectures. Noqualifiedsurvivor/formaldispatch. r443latehistoryFAIL,r444inertverifierdot/rootpunctuationambiguity,r446counter-continuityFAIL(noovercapinferred),r447late-registryFAIL retained. Rootallintakesmetadata/provenance/routingonly notindependentmathematicalvalidation.\n'
steering+='\nBOOKKEEPING: charge_search.py additionalIMMUTABLEhelper,THIRTEENbindings. BeforeEACHnativeSEARCH persist exactplan top-levelqueries list; invoke ABSOLUTEcharge_search.py ownplanpath UNDERrun.py. Helper authenticates liveoldcounters+chargeledger BEFOREmutation,rejectsduplicate/exhaustion,writesviaownwriter. NEVERdirectbudget/chargeledgeredit. Aftercharge exactnativecallONCE,FULLactualresponseIMMEDIATELYsavedbeforeotherwork. Wholelane3calls9queries,failedattemptsstaycharged,no refund/reset/backfill. GETsolefixedguard. Before significantinvestment reconcile exactIDkeys/scalarIDs AND exactsourceURLhistorymatches/read actualrelevantdispositions,noneighbortransfer;readactualsourceown/strongertheoremproofsbeforeclaimingnew. Standalonefirsttwocommandsno dot/prosepunctuation. Inertownverifierargumenttrue0/all13checkedundercaps recordedinvocationdeviation notautomaticexternalpolicybreach/abandonment. Genuineprotected/frozen/access/cap/network/budgetviolationsretainSTOP/disclosure.\n'
tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(steering),tail,count=1,flags=re.S)
ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+'#complete-metadata-r453','exec'),ns)
rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&peer_ids;assert not {x.get('source_url') for x in rr['rows']}&peer_sources
fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==13 and all(sha(Path(n))==h for n,h in fb.items()) and not (L/'bootstrap-receipt.json').exists()
ready=dict(utc=now,lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],frozen=13,model='gpt-6.1-sol',reasoning='high',service='default',accepted_new=57,target_new=60,latest_denials=str(denpath),credit=0)
save(ROOT/'r453-ready.json',ready)
print(json.dumps(dict(accepted_new=57,manifest_files=121,original_bindings=20,frozen_bindings=13,receipt_exit_counts=report['receipt_exit_counts'],ready=ready)))
