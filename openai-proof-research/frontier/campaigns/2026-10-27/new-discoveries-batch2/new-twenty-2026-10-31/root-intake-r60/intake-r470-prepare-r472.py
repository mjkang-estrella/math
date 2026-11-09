"""Root documentary integrity and bounded dispatch preparation only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r470'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
routing=json.loads((ROOT/'selection-routing-r470.json').read_text());assert sha(A/'TASK.txt')==routing['task_sha256'] and sha(A/'reservation.json')==routing['reservation_sha256']
manifest=json.loads((A/'byte-manifest.json').read_text());entries={x['path']:x for x in manifest['files']};assert len(entries)==161
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=manifest['terminal_non_circular_exclusions'];assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());prov=json.loads((A/'literal-bindings.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1]
 assert dg(raw)==row['raw_sha256'] and row['newline'] is True and raw.endswith(b'\n') and (A/f'literals/{key}.jsonl').read_bytes()==raw
 obj=json.loads(raw);assert obj==row['record'] and obj['mathdb_id']==int(key);sources[key]=obj['source_url']
 token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
 assert token.decode()==row['token'] and dg(token)==row['token_sha256'] and json.loads(token)==obj['statement']
 assert dg(obj['statement'].encode())==row['decoded_sha256'] and (A/f'literals/{key}.statement.txt').read_bytes()==obj['statement'].encode() and gates[key]['literal']==obj['statement']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget['calls_used']==3 and budget['queries_used']==9
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
previous=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==previous and sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries']
 expected=dict(previous);expected['calls_used']+=1;expected['queries_used']+=len(c['queries']);assert c['after']==expected;previous=expected
 assert json.loads((A/f"search-{['one','two','three'][i-1]}-response.json").read_text())
assert previous==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=7,success=5,unavailable=2)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
failures=[e for e in events if e['event']=='unavailable'];assert any(e['status']==403 and 'S0012365X04004066' in e['url'] for e in failures) and any('CERTIFICATE_VERIFY_FAILED' in e['error'] for e in failures)
history=json.loads((A/'history-access.json').read_text());assert len(history)==770;forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
audit=json.loads((A/'access-audit.json').read_text());assert audit['protected_saved_entries']==[] and audit['search_live_continuity_valid']
record=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'byte-manifest.json'),verified_manifest_files=161,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,routing_pins='Actual task/reservation hashes match retained ROOT genesis',runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Live old/new states, exact plan digests/querystrings, final counter/helper authenticated; full saved responses parsed',root_disposition='ZERO_QUALIFIED_SURVIVORS_376948_AUTHOR_INTENDED_RANGE_PROOF_SCIENTIFIC_PARK',scientific_summary='376948author complete explicittwo-tightfacet ridgeadjacencyproof claimed allm2n>=m+2 intendedcone, notindependentlyvalidated; literaldiametertwoclause has sourceknownm2n4cubeexception andm1nonnegativitynotfacet, corrections0. Actual2002DezaDutourcompanion onlyobstructionhalves/minimalendpoint, notfullpositivearbitrarynconstruction; sourcefinal2005unavailable403/PARK, no unsupportedroutineexclusion orformal.331982actual1512.01994v1sourceownstronger nucleusdiadembound pluskerinclusionfullpublic0;319970omittednormalizationRHwordingcorrection0;343095specificCao2018fullproofreportbodyunreadHOLD.379294allconfigurationpebblingone-thirdcoverinvariant unpaid;321467nonBSPsurjectivecoloringlowcolourinjection unpaid, alternatinginclusionexclusionnotcoefficientproof. Fourassignedoriginalsread,sixteenunread;fivePDFpayloadsincludingdistinctcompanion.',all20_gates=gates,new_denials=failures,process='Two ordinary source failures retained(TLSauthorbibliographyand403finalarticle), no retry/alternate delivery reported. Actualsaved770historyrecords no protectedcomponents; byte/frozen integrity doesnotassertuniversalcompliance. Native/transient/writer peaks unknown; materialtruncations/readfigure limits retained.',root_scope='Documentary integrity/routing only; no root mathematical solving/programs/Lean/checkers or protected externalpathfollow',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'expanded-corpus-r470-parent-integration.json',record)
den=json.loads((ROOT/'inherited-denials-r472.json').read_text());den['utc']=now
for e in failures:
 den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(e['url']).hostname.lower()+unquote(urlsplit(e['url']).path).rstrip('/')})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.1016/j.disc.2004.04.022','s0012365x04004066','math/0005270','small cones of m-hemimetrics','micheldeza.altervista.org/lpubhyperlink.html'})
for e in failures:
 final='S0012365X04004066' in e['url']
 den['records'].append(dict(url=e['url'],reason=dict(status=e['status'],artifact='Deza-Rosenberg Small cones of m-hemimetrics DiscreteMath291(2005),DOI10.1016/j.disc.2004.04.022/PIIS0012365X04004066/originalmath0005270' if final else 'MichelDeza officialpublicationbibliographymetadata artifactlpubHyperlink.html',restriction='Entireidentifiedarticle ALLnewhost/query/version/arxiv/author/cache/mirror/DOI/API/body/metadata deliveries unavailable. Explicitpre-denialoriginalonly,notfinalequivalence. DistinctDezaDutour2002math0201011companionnotdeniedbythisdifferentworkfailure.' if final else 'Identifiedbibliographymetadataartifact unavailable ALLnewalternatehosts/versions/cache/mirror/API/delivery; no TLS/HTTPupgrade workaround or indirectreconstruction. This doesNOTdeny every distinct paper by this author.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
den['root_r470_scope']='376948author intendedm2/ridgeproofPARK, literalcube/m1corrections0; finalSmallcones2005DOI10.1016/j.disc.2004.04.022/PIIS0012365X04004066/originalmath0005270 403ALLnewworkdeliveryunavailable. AuthorbibliographylpubHyperlinkTLScertfailuremetadataartifactonlynotallpapers. Distinct2002math0201011companionnotdenied; obstructionhalves/notfullpositiveproof.331982sourceownfull0,319970normalizationcorrection0,343095Cao2018bodyunread;pebbling/surjectiveswapgaps.161ownfiles20originalbindings13frozenverified,7GETattempt5PDF2failures,3search9queries,770ownaccessrecords no protectedcomponents.57/60unchanged.'
denpath=ROOT/'inherited-denials-r473.json';save(denpath,den)
base=json.loads((ROOT/'r471-config.json').read_text());steering=base['steering']+'\nLATESTr469completedzero:320587truncatedsimplex lowerconstruction paid butfullupper/equality/fiberdeficit unpaid;318479conditionalpolytopegrowth route now assigned independent LR investigation, do notduplicate;318895/318896Eisenstein gluing/metricreconstruction unpaid, realisometry notcomplexHermitianvaluepreservation.317704/316577sourceownpublic0;318272actualChebotarev2610.14100v3L7-8Th9analyticpublicrefutation0;318033sourceinitialcoefficientcorrection/corrected2distantpublic0,3distantproofunread.\nLATESTr470zero:376948author uniformintendedrange ridgeproof isscientificPARK, notindependentPASS; literalcubeexception/m1rangecorrections0. Actual2002math0201011 companion suppliesonlyobstructionhalves/minimalendpoint, notfullpositiveadjacencyproof. Final2005Smallconesofmhemimetrics DOI10.1016/j.disc.2004.04.022/PIIS0012365X04004066/originalmath0005270 returned403: ENTIREidentifiedworkALLnewalternatehosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata unavailable; explicitpre-denialoriginalonlynotfinalequivalence. Different2002companion isnotdenied. MichelDeza officialbibliographylpubHyperlink.htmlfailedTLScertificate: identifiedMETADATAartifactALLalternatedelivery unavailable,noTLS/HTTPupgrade/indirectrestore;NOTblanketban allauthorpapers.331982sourceownfullpublic0,319970normalizationcorrection0,343095specificCao2018proofunreadHOLD;379294allconfigurationpebbling and321467lowcolour nonBSP injection gaps.161ownfiles20originalbindings13frozen/770ownsavedaccessrecords verified; no newcredit,57/60.\n'
config=dict(base);config.update(number=472,protected_peers=['expanded-corpus-r471',RNAME:='lr-translation-degree-source-proof-review-sol-r1'],peer_routing_files=['selection-routing-r471.json','selection-routing-lr-degree-review-r1.json'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{469,470}),denials=str(denpath),steering=steering,year_floor=2000,candidate_pool=400)
save(ROOT/'r472-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());assert all(not any(t in part.lower() for t in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
R=P/RNAME;rr=json.loads((ROOT/'lr-degree-review-r1-ready.json').read_text());assert not (R/'bootstrap-receipt.json').exists() and sha(R/'TASK.txt')==rr['task_sha256']
assert all(sha(Path(n))==h for n,h in json.loads((R/'frozen-inputs.json').read_text()).items())
save(ROOT/'lr-degree-review-r1-prelaunch-addendum.json',dict(utc=now,immutable_inputs_unchanged=True,task_sha256=rr['task_sha256'],actual_protected_peers=['expanded-corpus-r471','expanded-corpus-r472'],additional_unavailability=den['records'][-2:],restriction='Supersedingdispatchsteeringonly;nofrozenmodifications. Applybothwork-specificdenialsmanuallybeforeanyGET evenifoldsnapshotdoesnotencodekeys. Metadatafailuredoesnotdenyallpapers.'))
print(json.dumps(dict(accepted_new=57,manifest_files=161,original_bindings=20,frozen_bindings=13,receipt_exit_counts=record['receipt_exit_counts'],new_unavailable_artifacts=2,discovery=ready,review_frozen_unchanged=True)))
