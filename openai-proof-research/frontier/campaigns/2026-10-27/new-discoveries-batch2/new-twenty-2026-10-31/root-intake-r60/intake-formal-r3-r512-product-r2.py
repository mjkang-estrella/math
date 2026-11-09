"""Root documentary artifact/provenance verification only; no mathematical execution."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,base64
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
F=P/'high-girth-ur-matching-formal-sol-r3';A=P/'expanded-corpus-r512';R=P/'product-measure-dimension-primary-qualification-sol-r2'
fex=manifest(F,'MANIFEST.json',213,'seal_checkpoint_57','self_exclusions');frozen(F,39)
assert sha(F/'TASK.txt')==read(ROOT/'high-girth-ur-matching-formal-r3-ready.json')['task_sha256']
failures={n+'.receipt.json':1 for n in ['base_first_07','diagnose_limits_09','base_kernel_12','base_partition_16','base_finite_19','base_sym2_21','finite_first_29','deletion_first_35','inventory_first_43','inventory_repaired_45','negative_loop_54']};failures['inventory_typed_47.receipt.json']=250
frec=receipts(F,failures);assert read(F/'seal_checkpoint_57.receipt.json')['exit']==0
pins=read(F/'PINS.json');result=read(F/'results/338806.json');assert result['formal_status']=='INCOMPLETE' and result['credit']==0 and result['scientific_status']=='HOLD'
def jsonrows(q):
 out=[]
 for line in q.read_text().splitlines():
  try:v=json.loads(line)
  except ValueError:continue
  if isinstance(v,dict):out.append(v)
 return out
pairs=[('URMatchingBase','base_minimal_24','base_minimal_kernel_25'),('URMatchingFinite','finite_repaired_31','finite_kernel_32'),('URMatchingDeletion','deletion_repaired_37','deletion_kernel_38'),('URMatchingControls','controls_first_52','controls_kernel_53')]
green=[]
for module,cl,kl in pairs:
 c=next(x for x in jsonrows(F/(cl+'.output.txt')) if x.get('stage')=='compile' and x.get('module')==module)
 k=next(x for x in jsonrows(F/(kl+'.output.txt')) if x.get('stage')=='check' and x.get('module')==module)
 assert c['exit']==k['exit']==read(F/(cl+'.receipt.json'))['exit']==read(F/(kl+'.receipt.json'))['exit']==0
 source=sha(F/'src'/(module+'.lean'));olean=sha(F/'build'/(module+'.olean'))
 assert c['source_sha256_before']==c['source_sha256_after']==k['source_sha256_before']==k['source_sha256_after']==source
 assert c['olean_sha256_after']==k['olean_sha256_before']==k['olean_sha256_after']==olean
 assert c['argv'][0]==pins['lean_bin'] and all(x in c['argv'] for x in ['-j1','-M3500','-DwarningAsError=true']) and k['argv']==[pins['leanchecker_bin'],module]
 assert c['LEAN_PATH']==k['LEAN_PATH']==':'.join([str(F/'build')]+pins['upstream_lean_paths']) and c['LEAN_NUM_THREADS']==k['LEAN_NUM_THREADS']==1
 green.append(dict(module=module,source_sha256=source,olean_sha256=olean,compile=cl,checker=kl,compile_receipt_sha256=sha(F/(cl+'.receipt.json')),checker_receipt_sha256=sha(F/(kl+'.receipt.json'))))
assert result['strict_green_modules']==[x['module'] for x in green]
replay=jsonrows(F/'partial_replay_50.output.txt');assert len(replay)==6 and all(x['exit']==0 and x['source_before']==x['source_after'] for x in replay)
for x in replay:
 assert x['LEAN_PATH']==':'.join([str(F/'replay/checkpoint01/build')]+pins['upstream_lean_paths'])
 if x['stage']=='checker':assert x['olean_before']==x['olean_after']
audit=next(x for x in jsonrows(F/'inventory_typed_47.output.txt') if x.get('stage')=='compile');assert audit['exit']==-6 and audit['olean_sha256_after'] is None

aex=manifest(A,'MANIFEST.json',156,'manifest_finalize','terminal_noncircular_self_exclusions');frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r512.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'originals.json');assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 normalized=dict(v,raw_sha256=v['raw_line_sha256']);raw,obj,token=corpus(normalized)
 assert base64.b64decode(v['raw_line_base64'])==raw and (A/'raw'/f'{key}.jsonl').read_bytes()==raw and obj==v['object'] and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==gates[key]['literal_statement'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'];sources[key]=obj['source_url']
abudget=search(A,2,6,3,9,['search1-response.json','search2-response.json']);ae=guard(A,[q for q in (A/'plans').glob('*.json') if 'url' in read(q)],ids,dict(attempt=10,success=10),9)
history=read(A/'history-access.json')['access'];allow=read(A/'historical-results-allowlist.json');assert len(history)==881
for x in history:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']

rex=manifest(R,'MANIFEST.json',106,'seal_manifest','terminal_noncircular_exclusions');frozen(R,30)
assert sha(R/'TASK.txt')==read(ROOT/'product-measure-dimension-qualification-r2-ready.json')['task_sha256']
rrec=receipts(R,{'read_accessibility.receipt.json':1,'get_lie_primary.receipt.json':1,'get_suck_primary.receipt.json':1})
rbudget=search(R,2,5,2,6,['fullresponses/search-one.json','fullresponses/search-two.json']);revents=guard(R,list((R/'plans').glob('get-*.json')),[364140],dict(attempt=3,success=1,unavailable=2),1)
v=read(R/'inputs/provenance364140.json');raw,obj,token=corpus(v)
assert raw==(R/'inputs/original364140.raw.jsonl').read_bytes() and obj==read(R/'inputs/literal364140.json')==read(R/'reservation.json')['rows'][0] and obj['mathdb_id']==364140
assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['decoded_sha256']
assert read(R/'review.json')['364140']['disposition']=='ORDINARY_PASS_SCIENTIFIC_HOLD'
fs='338806 uncreditedformalr3 INCOMPLETE,NOliteralnegation/paper. Fouractualstrict/kernelgreenmodules verifiedbyte/log/receipt: Base(model),Finite(attainedmaxima/universalbounds/UR<=nu),Deletion(lostedgeinjection/cardbound,inducedtransportUNPAID),Controls(singleedge/emptygraph);no fullsource/girth/quantifierbridge. Partialemptybuildsource-onlyreplay exactlyFIRST3modules6actual0exits/upstreamonlyLEANPATH,notfullendpoint/controlreplay. Scoped23declaxiomprintpermittedtrio REPORTONLYnotfullbodyaudit. BodyinventoryactualLean-6/runner250threadcreationfailurealready-j1/env1,unpaid;allimport/header/type/audit/negativecontrolfailuresretained.213manifestfiles39frozen/fourcompile-checksource/oleansposthashesverified;no rootLeanexecution. ROOTcontinuesUNCREDITEDofflineformalresearch,scientificHOLD/zeroacceptanceremain. Exactunpaidledger/results retained; no source/currentregistry/finalbodywaiver,credit0/57unchanged.'
ass='r512 zeroqualifiedsurvivors.340014 exact2025publicweakacyclicmatchingtheoremproof/prime-empty-infinitebridge0;347986 specificpublicK36,n12coloringcertificatevalidityunpaidHOLD,personalmod3onlyknownfamily;344879 all-n tightprefix residue/slopegapunpaid.353119sourceownrefutation0,375408sourceTh1.4/Section4public0;340080gamevsordinarysaturation/oddcyclefamilycorrection0.156manifestfiles20corpusbindings13frozen881savedhistorynamesverified;10GETsuccess9PDF1HTML,2search6strings,nonewdenial. TextEncoderfirstresponseserializationfailurehonestlyrecoveredSAMEstoredresponseNEXTtoolcall,no refetch/refund/reset;toolsfailurequalifiednotuniversalprocessclearance. Remaining14originalbodiesunread/nofigures/finalcorrection/wholebody/currentregistryproofclearance. Noformaldispatch/credit.'
rs='364140 retainedSOURCEDrepairedordinaryPASS/scientificPARK. ActualAyala-Kizil2016Kybernetika52(6)837-847full11pageprimarytheorems/proofsread,coveringsemigroup/formalseries/measurable-signedcontrolstatementnotONEfinitepositivewordJacobian/no normalizedP_mdim;boundednonmatchcomplete,no blanketLie-theoryexclusion. ActualSuck2002andJurdjevic-Sussmann1972primaryrequests403beforebodies;bothENTIREworksclosed,actualproofparametercoverageUNREAD/specificHOLD. No public/routineexclusion/noveltyqualification,formalupperLie-shuffle/dimensioninfrastructureunpaid.106manifestfiles30frozen1corpusbindingverified;3GET1PDFsuccess2distinct403/no retries,2search5strings;headinglookupdocumentaryexit1retained,full2016bodymaterialglyphsread,oldsourceWileyclosure/finalHOLDpreserved. Noformaldispatch/credit,57unchanged.'
fr=dict(utc=now,mathdb_id=338806,source_lane=str(F),manifest_sha256=sha(F/'MANIFEST.json'),verified_manifest_files=213,verified_frozen_bindings=39,green_modules=green,runner_receipts=frec,partial_replay_modules=3,partial_replay_actual_exits=[x['exit'] for x in replay],body_audit_unpaid=True,result=result,scientific_summary=fs,root_disposition='INCOMPLETE_UNCREDITED_FORMAL_RESEARCH_CONTINUE',credit=0,accepted_new=57,terminal_self_exclusions=fex,root_scope='Documentary integrity only; no Lean/math execution by root.')
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=156,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=881,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex)
rr=dict(utc=now,mathdb_id=364140,source_lane=str(R),manifest_sha256=sha(R/'MANIFEST.json'),verified_manifest_files=106,verified_frozen_bindings=30,verified_original_bindings=[364140],review=read(R/'review.json'),source_map=read(R/'source-map.json'),runner_receipts=rrec,guard_events=dict(collections.Counter(e['event'] for e in revents)),search_budget=rbudget,new_unavailable=read(R/'new-unavailable.json'),scientific_summary=rs,root_disposition='SCIENTIFIC_PARK_SPECIFIC_CLOSED_PRIMARY_PROOFS_UNPAID',credit=0,accepted_new=57,formal_dispatch=False,terminal_self_exclusions=rex)
den=read(ROOT/'inherited-denials-r525.json');den['utc']=now;den['root_highgirth338806_formal_r3_scope']=fs;den['root_r512_scope']=ass;den['root_product_dimension364140_r2_scope']=rs
identities=[('0022039672900356','Jurdjevic-Sussmann Control systems on Lie groups JDE12(2)(1972)313-329','10.1016/0022-0396(72)90035-6'),('S0165489602000203','Reinhard Suck Independent random utility representations MathematicalSocialSciences43(3)(2002)371-389','10.1016/S0165-4896(02)00020-3')]
for needle,work,doi in identities:
 failure=next(x for x in revents if x['event']=='unavailable' and needle in x['url']);assert failure['status']==403
 den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'doi.org/'+doi.lower()});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),doi.lower()})
 den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact=work,restriction='ENTIRE identified work ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable;no retry/identitycorrection/alternaterecovery. Distinct successfulAyala-Kizil2016paper notdenied.'),evidence=dict(path=str(R/'new-unavailable.json'),sha256=sha(R/'new-unavailable.json'),guard_sha256=sha(R/'guard-ledger.jsonl'))))
# All completed-packet documentary checks precede root mutations.
save(P/'high-girth-ur-matching-formal-parent-integration-r3.json',fr);save(P/'expanded-corpus-r512-parent-integration.json',ar);save(P/'product-measure-dimension-primary-parent-integration-r2.json',rr);save(ROOT/'inherited-denials-r526.json',den)
save(ROOT/'formal-r3-r512-product-r2-intake-report.json',dict(utc=now,files=dict(formal=213,r512=156,product=106),frozen=82,corpus_bindings=21,verified_green_modules=green,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(files=475,frozen=82,corpus_bindings=21,green_modules=[x['module'] for x in green],credit=0,accepted_new=57)))
