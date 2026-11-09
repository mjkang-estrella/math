"""Root documentary provenance checks and disjoint metadata routing only."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
records={};chunks={};forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for number,nfiles,nhistory in [(476,149,788),(477,151,789)]:
 a=P/f'expanded-corpus-r{number}';routing=json.loads((ROOT/f'selection-routing-r{number}.json').read_text())
 assert sha(a/'TASK.txt')==routing['task_sha256'] and sha(a/'reservation.json')==routing['reservation_sha256']
 if number==476:
  mname='SHA256-MANIFEST.json';m=json.loads((a/mname).read_text());entries={x['path']:x for x in m['files']};exclusions=m['terminal_noncircular_self_exclusions']
  for n,v in entries.items():
   assert not Path(n).is_absolute() and '..' not in Path(n).parts
   q=a/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
 else:
  mname='MANIFEST.sha256';entries={}
  for line in (a/mname).read_text().splitlines():
   h,n=line.split('  ',1);assert len(h)==64 and re.fullmatch('[0-9a-f]{64}',h) and n not in entries
   assert not Path(n).is_absolute() and '..' not in Path(n).parts
   q=a/n;assert not q.is_symlink() and sha(q)==h,n;entries[n]=h
  exclusions=['MANIFEST.sha256','manifest_finish.receipt.json','manifest_finish.output.txt']
  text=(a/'MANIFEST-EXCLUSIONS.md').read_text();assert all(n in text for n in exclusions)
 assert len(entries)==nfiles
 assert {str(q.relative_to(a)) for q in a.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
 frozen=json.loads((a/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(Path(n).parent==a and sha(Path(n))==h for n,h in frozen.items())
 after=json.loads((a/'frozen-after.json').read_text());assert after['count']==13 and after['mismatches']==[]
 prov=json.loads((a/('originals.json' if number==476 else 'original-provenance.json')).read_text());gates=json.loads((a/'results.json').read_text());ids=json.loads((a/'reservation.json').read_text())['ids']
 assert len(ids)==len(prov)==20 and set(ids)==set(map(int,gates))=={x['id'] for x in prov};sources={}
 for row in prov:
  q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw);key=str(row['id'])
  assert obj['mathdb_id']==row['id'] and row['newline'] is True and raw.endswith(b'\n') and (a/'originals'/f'{key}.jsonl').read_bytes()==raw
  if number==476:
   assert row['raw_line'].encode()==raw and dg(raw)==row['raw_sha256']
   token=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
   assert token.decode()==row['raw_statement_token'] and dg(token)==row['raw_statement_token_sha256'] and json.loads(token)==row['decoded_statement']==obj['statement']==gates[key]['literal_statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256']
  else:
   assert dg(raw)==row['raw_line_sha256'] and gates[key]['literal']['statement']==obj['statement']
   for field,v in row['statement_tokens'].items():
    token=re.search(('"'+re.escape(field)+'"\\s*:\\s*("(?:[^"\\\\]|\\\\.)*")').encode(),raw)[1]
    assert base64.b64decode(v['raw_token_base64'],validate=True)==token and dg(token)==v['raw_token_sha256'] and json.loads(token)==obj[field] and dg(obj[field].encode())==v['decoded_utf8_sha256']
  sources[key]=obj['source_url']
 receipts=[]
 for q in sorted(a.glob('*.receipt.json')):
  v=json.loads(q.read_text());assert v['cwd']==str(a) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
  receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
 budget=json.loads((a/'search-budget.json').read_text());assert budget==dict(calls_used=3,queries_used=9,maximum_calls=3,maximum_queries=9,charged_before_call=True)
 charges=[json.loads(s) for s in (a/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==3
 prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
 for i,c in enumerate(charges,1):
  assert c['sequence']==i and c['before']==prev and sha(a/c['plan'])==c['plan_sha256'] and json.loads((a/c['plan']).read_text())['queries']==c['queries']
  nxt=dict(prev);nxt['calls_used']+=1;nxt['queries_used']+=len(c['queries']);assert c['after']==nxt;prev=nxt
  response=(a/(f'search{i}-response.json' if number==476 else f'search-response{i}.json')).read_text()
  assert isinstance(json.loads(response),str) if number==476 else bool(response.strip())
 assert prev==budget and sha(a/'charge_search.py')==sha(ROOT/'charge_search.py')
 events=[json.loads(s) for s in (a/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events)
 assert counts==(dict(attempt=10,success=7,redirect=2,unavailable=1) if number==476 else dict(attempt=7,success=7))
 for e in events:
  if e['event']=='success':assert sha(a/e['destination'])==e['sha256'] and (a/e['destination']).stat().st_size==e['bytes']
 history=json.loads((a/'history-access.json').read_text());assert len(history)==nhistory
 assert all(not any(t in part.lower() for t in forbidden) for x in history for part in Path(x['path']).relative_to(P).parts)
 assert all(not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466]) for x in history)
 records[number]=dict(utc=now,source_lane=str(a),task_reservation_genesis_verified=True,manifest_sha256=sha(a/mname),verified_manifest_files=nfiles,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,search_counter_continuity='Three live before/afterstates,exactplans/querystrings,immutablehelper andfullsavedresponsesverified.',root_disposition='ZERO_QUALIFIED_SURVIVORS',root_scope='Documentary verification/routing only,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
records[476].update(scientific_summary='318314/318315actualPoddarSawantShankar2603.14508v2June8,2026Theorem1.3Cor1.4fulljointrefinedpermutationproofSection7read,exactS10/S12/T1/T2/T3/S17bridgepublic0;notmarginal-onlyequidistribution.321441sourceProp3.9groveclosure refutation andLemma3.8equivalence-onlyreadingbothpublic0,scopekeptseparate.318375fixedcompositionrun-countidentitypaid,butShannonentropy/Jensenwrongdirectiondonotpayfiniteexpectedplug-inentropyinequality.377726lowerboundrankchoice/deletion/multiplicitygaps;searchstrongerconstructiononlynavigation/notauthenticatedrefutation.380347generalself-pairedorbitalalgebra proofsource-dependent;independentnine-typeclassification/selftransposecertificate/prior/significanceunpaid,notallc-generalization or qualifiedsurvivor.',
 reading_limits='Fourteenassignedoriginalbodiesunread; actualmaterialtheorem/proofpassagesonly,novisualfigures/tableaudit. Tableclassificationattributed,nocomputationhere.',
 process='788savedhistoricalpathnameschecked,no protected externalpathfollow. TwoUTF8failures(seconddecoderrepeatedbeforeLatin1fix),absent-labelValueError andfinalHTTP403retained,notdeleted.10GETchargedhops7transport(6PDF+authorbibliography),2redirects1HTTP403. Allsource-specificblocksretained,noalternateafterfailure. Native/transient/writerpeaksunknown,nouniversalcomplianceclaim.')
records[477].update(scientific_summary='318553treepebblingconditionalpartitionbounddoesnotpayallgraphs:BFSrootdistancesnotpairwisegraphdiameter,shortcut-sensitivepartition/integralobstructionunpaid.376921cut-freeplanarselfdualall-nrealizationnotpaidbyblockmultiplication(cutvertex)oronewheel45example;literalquantifiercorrection0.378650actualMatolcsiVinuesa2009publicmatchingautoconvolutioncounterclaim20stepbodyread,decimalcoeffsnotindependentexactcertificate/notnewresult.320289sourceWangZhu1008.2605Prop3.1strongerallparameterlogconcavity0;378992actualAthanasiadisTzanakimath0606018Th1.1(i)emptydeletion/reduciblejoinbridgepublic0;320930actualArmstrongStumpThomas1101.1277Theorem1.2allthreePanyushevclaimsSection6public0,exceptionalcomputationalinputsattributednotreaudited.',
 root_intake_repair='First root verifier stopped before mutations: assumed .json-suffixed search responses were JSON. All three r477 files are full plain native-response text; format inspected and verification corrected. Author evidence unchanged.',
 reading_limits='Fiveassignedoriginalworksreadatstateddepth,fifteenunread,twofollowups,novisualfigures. OtherliteralpublicclaimsremainbodyHOLDwhereunread,notautomaticexclusion.',
 process='789savedhistoricalpathsnamechecked;8broadtext-hitfilesstructurallyreconciled,nomatchingneighborscopeautomaticallytransferred,noexternalpathfollow.7PDFGETsuccess,3search9queries,no newdenials. Unrecoveredbroaderroutingtextnotusedmathematicalevidence,materialtheoremtruncationsrecovered. Native/transient/writerpeaksunknown,nouniversalcomplianceclaim.')
# Mutations only after both packets have passed verification.
for n,v in records.items():save(P/f'expanded-corpus-r{n}-parent-integration.json',v)
den=json.loads((ROOT/'inherited-denials-r481.json').read_text());den['utc']=now;a=P/'expanded-corpus-r476';unavailable=json.loads((a/'new-unavailable.json').read_text());plan=json.loads((a/'get-superpattern-final.json').read_text());url=plan['url']
den['blocked_keys']=sorted(set(den['blocked_keys'])|{urlsplit(url).hostname.lower()+unquote(urlsplit(url).path).rstrip('/'),'zbmath.org/emis'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'10.37236/1692','math/0212343','packing patterns into words','v9i2r20.pdf'})
den['records'].append(dict(url=url,reason=dict(status=unavailable['outcome'],artifact=unavailable['work'],restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable,no retry or indirectrecovery. Explicitpredenialoriginalonlynotfinalequivalence. Redirectendpointfailed403;guardhistoryunchanged. This iswork-specific,notblanketdenialofallEJCpapers.'),evidence=dict(path=str(a/'new-unavailable.json'),sha256=sha(a/'new-unavailable.json'),guard_sha256=sha(a/'guard-ledger.jsonl'))))
scope476=records[476]['scientific_summary']+' NEW Packing Patterns into Words EJC9(2)R20 DOI10.37236/1692/originalmath0212343 finalKyotoEMISredirectedemis.de->zbmath/emis403: ENTIREidentifiedworkALLNEWhosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadataUNAVAILABLE,noalternate/retry/indirectrecovery. Explicitpredenialoriginalonlynotfinalequivalence.149ownfiles20bindings13frozen788savedhistorypathsverified,10chargedGET7success2redirect1HTTP403,3search9queries;allfailuresretained.57/60unchanged.'
scope477=records[477]['scientific_summary']+'151ownfiles20bindings13frozen789savedhistorypathsverified,7PDFGETsuccess3search9queries,nonewdenials/credit/dispatch.57/60unchanged.'
den['root_r476_scope']=scope476;den['root_r477_scope']=scope477;denpath=ROOT/'inherited-denials-r482.json';save(denpath,den)
base=json.loads((ROOT/'r478-config.json').read_text());steering=base['steering']+'\nLATESTcompletedr476:'+scope476+'\nLATESTcompletedr477:'+scope477+'\n';completed=sorted(set(base['completed_discovery_numbers'])|{476,477})
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=[]
for number,other,peers in [(479,480,['selection-routing-r478.json']),(480,479,['selection-routing-r478.json','selection-routing-r479.json'])]:
 config=dict(base);config.update(number=number,protected_peers=['expanded-corpus-r478',f'expanded-corpus-r{other}'],peer_routing_files=peers,completed_discovery_numbers=completed,denials=str(denpath),steering=steering,year_floor=2000,candidate_pool=400)
 save(ROOT/f'r{number}-config.json',config);rd=module.prepare(config)
 allow=json.loads((Path(rd['lane'])/'historical-results-allowlist.json').read_text())
 assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
 assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466]) for x in allow)
 ready.append(rd)
assert not set(ready[0]['ids'])&set(ready[1]['ids'])
save(ROOT/'r476-r477-completion-boundary-delta.json',dict(utc=now,message=scope476+'\n'+scope477,new_protected_peers=['expanded-corpus-r479','expanded-corpus-r480'],immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(accepted_new=57,intakes={str(n):dict(files=v['verified_manifest_files'],frozen=13,exits=v['receipt_exit_counts']) for n,v in records.items()},ready=ready)))
