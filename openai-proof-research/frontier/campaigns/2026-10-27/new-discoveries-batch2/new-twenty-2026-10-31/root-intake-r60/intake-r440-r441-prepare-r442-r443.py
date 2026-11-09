import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil
from urllib.parse import urlsplit,unquote
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();ledger=json.loads((P/'ledger.json').read_text());assert ledger['accepted_new']==57
reports=[];den=json.loads((ROOT/'inherited-denials-r440.json').read_text());den['utc']=now
for num,mname,expected in [(440,'SHA256-MANIFEST.json',142),(441,'MANIFEST.sha256.json',160)]:
 A=P/f'expanded-corpus-r{num}';m=json.loads((A/mname).read_text());mf=m['files'];files={x['path']:x['sha256'] for x in mf} if isinstance(mf,list) else {n:(v['sha256'] if isinstance(v,dict) else v) for n,v in mf.items()}
 assert len(files)==expected and all(sha(A/n)==v for n,v in files.items())
 frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==12 and all(sha(Path(n))==v for n,v in frozen.items())
 after=json.loads((A/'frozen-after.json').read_text());assert after['count']==12 and after['mismatches']==[]
 reservation=json.loads((A/'reservation.json').read_text());ids=reservation['ids'];gates=json.loads((A/'results.json').read_text());assert len(ids)==20 and set(ids)==set(map(int,gates))
 prov=json.loads((A/('literal-provenance.json' if num==440 else 'provenance.json')).read_text());rows=list(prov.items()) if isinstance(prov,dict) else [(str(x['id']),x) for x in prov];assert len(rows)==20
 chunks={};bindings=[]
 for idstr,row in rows:
  q=Path(row['chunk'])
  if str(q) not in chunks:
   b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
  h,lines=chunks[str(q)];raw=lines[row['line']-1];obj=json.loads(raw);assert h==row['chunk_sha256'] and obj['mathdb_id']==int(idstr) and raw.endswith(b'\n')
  tok=re.search(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)[1]
  if num==440:
   assert raw==bytes.fromhex(row['raw_line_hex']) and dg(raw)==row['raw_line_sha256'] and raw[-1:].hex()==row['newline_hex']
   assert tok==bytes.fromhex(row['statement_token_hex']) and dg(tok)==row['statement_token_sha256'] and obj['statement']==row['decoded_statement'] and dg(obj['statement'].encode())==row['decoded_statement_sha256']
  else:
   assert raw==(A/'originals'/f'{idstr}.jsonl').read_bytes() and dg(raw)==row['raw_sha256'] and row['newline'] and raw[-1:].hex()==row['newline_bytes_hex']
   assert tok==row['statement_raw_token'].encode() and dg(tok)==row['statement_raw_token_sha256'] and obj['statement']==row['statement_decoded_utf8'] and dg(obj['statement'].encode())==row['statement_decoded_utf8_sha256']
  bindings.append(dict(id=int(idstr),chunk=str(q),line=row['line'],raw_sha256=dg(raw),token_sha256=dg(tok),statement_sha256=dg(obj['statement'].encode())))
 assert set(x['id'] for x in bindings)==set(ids)
 prev='0'*64;events=[]
 for i,b in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
  e=json.loads(b);assert e['seq']==i and e['previous']==prev;prev=dg(b);events.append(e)
  if e['event']=='success':assert sha(A/e['destination'])==e['sha256']
 attempts=[e for e in events if e['event']=='attempt'];success=[e for e in events if e['event']=='success'];failed=[e for e in events if e['event']=='unavailable'];charges=collections.Counter(str(k) for e in attempts for k in e['routes']);assert max(charges.values())<=12
 assert (len(attempts),len(success),len(failed))==((15,13,1) if num==440 else (11,10,0))
 rec=[]
 exclusions=m['terminal_noncircular_self_exclusions']
 for n in [n for n in files if n.endswith('.receipt.json')]+[n for n in exclusions if n.endswith('.receipt.json')]:
  j=json.loads((A/n).read_text());rec.append(dict(path=n,sha256=sha(A/n),exit=j.get('exit'),killed=j.get('killed')))
 budget=json.loads((A/'search-budget.json').read_text());assert budget.get('calls_used',budget.get('actual_calls_precharged',budget.get('calls_charged')))==3 and budget.get('queries_used',budget.get('querystrings_precharged',budget.get('querystrings_charged')))==9
 access=json.loads((A/'access-inventory.json').read_text())
 disposition=('350044fullordinaryall-positive-tripartitepart/allforestlowerboundproposalPARKED actualJGTfinal10.1002/jgt.22812/2103.05294unavailable; independent/prior/significance/finalgatesunpaid, noformal.329239tableauweightinjection/skewADSgap;329238generalHallLittlewood-tbranchinggap;328767Snrow-sum/degree/zero-one-summandgaps.328499/325707actualAshrafProp11publicsamefamilyrefutationzero.' if num==440 else '323877actualsourcev2formula12vsactualwalkcount8atn3, sourcecorrectionzero;324271localinversionNOTglobalcounterexample, universalreroutingunpaid;332117completedKroneckerquotientgenerationpartial, exactPreRGB/POT/sameblock/BezoutC4bridgesunpaid. Other16primarybodiesunread; noqualifiedsurvivor orformaldispatch.')
 record=dict(utc=now,lane=str(A),manifest_files_verified=len(files),manifest_sha256=sha(A/mname),manifest_mismatches=[],frozen_verified=12,frozen_mismatches=[],frozen_after=after,literal_bindings=bindings,all20_gate_records=gates,receipts=rec,receipt_count=len(rec),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in rec)),guard_chain_verified=True,guard_tail_sha256=prev,GET_hops=len(attempts),transport_successes=len(success),unavailable=failed,GET_charges=dict(charges),search_calls=3,queries=9,access_inventory=access,root_disposition=disposition,root_role='Documentaryintegrity/orchestrationonly,no mathematicalprogram/compiler execution',credit=0,accepted_new=57,target_new=60,previous_accepted=39)
 save(P/f'expanded-corpus-r{num}-parent-integration.json',record);reports.append(dict(lane=str(A),manifest=len(files),frozen=12,bindings=20,receipts=len(rec),exits=record['receipt_exit_counts']))
 if num==440:
  e=failed[0];assert e['status']==403 and e['artifacts']==['10.1002/jgt.22812'];den['blocked_keys']=sorted(set(den['blocked_keys']+[e['url_key'],'doi.org/10.1002/jgt.22812']));den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+e['artifacts']+['2103.05294']))
  den['records'].append(dict(url=e['url'],reason=dict(status=403,artifact='Dong-Ge spanning trees containing a forest in multipartite graphs final DOI10.1002/jgt.22812 original2103.05294',restriction='Entire identified work unavailable ALLnewalternatehost/query/version/cache/mirror/arxiv/author/DOI deliveries; cachedoriginalonlywhereexplicitlycopied, no finalequivalence.'),evidence=dict(path=str(A/'guard-ledger.jsonl'),sha256=sha(A/'guard-ledger.jsonl'))))
  manual=access['manual_unavailable'];assert len(manual)==1 and manual[0]['challenge_offset']==90531
  ev=next(e for e in success if e['destination']==manual[0]['destination']);key=urlsplit(ev['url']).hostname.lower()+unquote(urlsplit(ev['url']).path).rstrip('/');den['blocked_keys']=sorted(set(den['blocked_keys']+[key]))
  den['records'].append(dict(url=ev['url'],reason=dict(artifact='Exact MathDB350044 currentrecord',status='Transport200challenge-suffix at byte90531',restriction='EntireexactrecordALLalternatedeliveryunavailable; noscript/API/cache/alternateURL/hostretry; guard success historyunchanged,nobackfill.'),evidence=dict(path=str(A/manual[0]['destination']),sha256=ev['sha256'],manual_classification=str(A/'access-inventory.json'))))
den['root_r440_r441_scope']='r440142hashes/r441160hashes+12frozeneach/all40originalbindings verified.350044ordinaryfulltripartiteforestlowerboundPARKED actualfinalJGT10.1002/jgt.22812/2103.05294body403ALLnewdeliverydenied,currentMathDB350044challengeunavailable; noformal. Spectral328499/325707actualpubliconefamilyzero.323877sandpileactualsourceformulaerrorzero;324271globaltreeorderingreroutingand332117exactproductcodePreRGB/POTscopeunpaid. R44111hops10payloads1allowedredirect,no newdenial. No mathematicalproofclearancefromrootmetadata.'
denpath=ROOT/'inherited-denials-r442.json';save(denpath,den)
base_source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();base_tail=base_source[base_source.index('# Metadata selector:'):];base_tail=base_tail[:base_tail.rfind('\nprint(')]
prior_ids=[];prior_sources=[];ready=[];wavelet='graph-wavelet-minimax-primary-comparison-sol-r2'
for num,other in [(442,443),(443,442)]:
 L=P/f'expanded-corpus-r{num}';assert not L.exists()
 tail=base_tail.replace('selection-routing-r434.json',f'selection-routing-r{num}.json').replace('for num in range(421,434):','for num in range(421,442):')
 tail=tail.replace("active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']",'active='+repr([f'expanded-corpus-r{other}',wavelet]))
 tail=tail.replace('peer_ids={326555,324571};peer_sources={\'https://arxiv.org/abs/1310.5240\',\'https://arxiv.org/abs/1211.6486\'}','peer_ids='+repr(set([326555,324571,332073]+prior_ids))+';peer_sources='+repr(set(['https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486','https://arxiv.org/abs/1512.05406']+prior_sources)))
 tail=tail.replace("'accepted_new':55","'accepted_new':57").replace('55/60','57/60')
 tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2','binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1']:")
 latest='''
LATESTROOT:57/60beyond39accepted96total;ONLYGPT-6.1Solhigh/defaultALLagents,nochildren. Accepted#56shoe324571allcountableuniformsup<=255/256<1and#57CMDRR326555universalnonexistence havefullindependentliteral/finalsource/body/kernel/source-onlyreplay/dependency-audit/paperPASS,rootacceptancesretainprioraccess/processqualifications,noglobalnovelty/universalhistoricalcomplianceclaim. Stale55/60credit0authorhandbacksarehistorical. Nohelpers/constant/finite-countablevariant/row-columnextra credits.
ACTIVEwavelet332073primarycomparison graph-wavelet-minimax-primary-comparison-sol-r2 andSIBLINGdiscovery entirelyprotectedfromread/hash/glob/list/poll evenmetadata. RootusesretainedIDs/sourceURLsforseparation. Waveletordinary/v1PASS strict4>2competingfullbasisWITHglobalmean; sourceEq7normalizedcutidealnotpremiseinAlgorithm1/Conj1. Specificsuccessorthesis(publicationauthor/dateidentityunverified,Chapter4Algorithm6/Th28-29)andfinalpublicationqualificationactive;sourceownunequalcommunityparagraphpotentialroutineobjectionrequirescompletebridge. Priorr1search1fullresponseNOTpersisted,ProcedureFAILretained,nooldcounterreset/backfill;newfocusedprimarycomparisonseparatelyauthorized8GET/2search6queries. Noformaldispatch/credityet.
Completedr440all0:350044fullordinarytripartiteforestboundproposalPARKED identifiedfinalJGT10.1002/jgt.22812/original2103.05294Wiley403ALLnewalternatebodydeliveryunavailable,cachedoriginalnotfinalequivalence,currentMathDB350044challenge-suffixunavailable. Noformal/newretrievallane.328499/325707actualAshrafProp11publicnegative-exponentrefutationonefamilyzero;329239weightedtableauinjection/skewADSgap,329238generalHL-tcouplinggap,328767Snrow-sum/degree/zero-one-summandgap. Completedr441all0:323877ownsourcev2visibleformula12atn3vswalkcount8,sourcecorrectionzero;324271localroot-orderinversionNOTglobalcounterexample/globalreroutingunpaid;332117quotientgenerationonlynotfullPreRGB/POT/sameblock/BezoutC4scope. Other16sourcebodiesunread. R44015hops13transportpayloads(1challenge),1redirect1final403;R44111hops10payloads1allowedredirect,no newdenial.3search9each,12frozenintacteach.
Earlier327053latticeordinaryproposalPARKEDfinalJNT10.1016/j.jnt.2014.02.015/1401.2891denied,MathDB327053/332073challengeunavailable;332892sumsetZ6MAXgammaordinaryproposalPARKEDMathematika10.1112/S0025579315000157/1307.8396denied;341052roundingordinary/probabilityPASSbutYe1999DOI10.1007/s10107980012aunavailableblockedHTTPredirect+final/significanceunpaid. Allnewalternatehost/query/version/cache/mirror/author/DOIdeliveryafterfailureforbidden;noHTTPupgrade/TLS/cookiebypass. Alloldr39576acquisitionsquarantined.
Readactualprimarydefinitions/strongerexistingtheoremsandproofsBEFOREmajorinvestment; namedconjecturecanalreadyfollowfromanothertheorem/ownexample. Publicresults/sourceownsolutions/routineCOMPLETEbridges/wording-domainendpointcorrectionsZERO. Noexclusionfromshortness/standardtool/smallnessalone. SpecificapplicableunreadtheoremHOLD,genericworldwideunknownnotautomaticveto,boundednonmatchnotworldwidenovelty. ExactIDkeys/sourcefieldsforhistory,neverhashdigitmatches/neighbor-dispositiontransfer. Rootintakesdocumentaryonly,noboundary/math/compilerexecution.
'''.replace('SIBLING',f'expanded-corpus-r{other}')
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(latest),tail,count=1,flags=re.S)
 ns=dict(globals());exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{num}','exec'),ns)
 rr=json.loads((L/'reservation.json').read_text());assert not set(rr['ids'])&set(prior_ids);prior_ids+=rr['ids'];prior_sources +=[x.get('source_url') for x in rr['rows']]
 task=(L/'TASK.txt').read_text();assert 'Resources fixed:' in task and 'wholelane maximum3 actual calls9' in task
 fb=json.loads((L/'frozen-inputs.json').read_text());assert len(fb)==12 and all(sha(Path(n))==v for n,v in fb.items()) and not (L/'bootstrap-receipt.json').exists()
 ready.append(dict(lane=str(L),task_sha256=sha(L/'TASK.txt'),ids=rr['ids'],role='research'))
save(ROOT/'r442-r443-ready.json',dict(utc=now,accepted_new=57,target_new=60,previous_accepted=39,completed_intakes=reports,packets=ready,active_wavelet=wavelet,latest_denials=str(denpath),model='gpt-6.1-sol',reasoning='high',service='default',credit=0))
print(json.dumps(dict(accepted_new=57,intakes=reports,packets=ready)))
