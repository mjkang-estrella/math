import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import hashlib,json,datetime,collections,shutil,ast
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
R=P/'cover-ratio-regular-mis-source-review-sol-r1'
L=P/'cover-ratio-primary-comparison-sol-r2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):
 assert not p.exists(),str(p)
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
assert not L.exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'MANIFEST.json').read_text());rows=m['files']
assert all(sha(R/x['path'])==x['sha256'] for x in rows)
f=json.loads((R/'frozen-inputs.json').read_text());assert all(sha(Path(s))==v for s,v in f.items())
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==234 and not after['mismatches']
receipts=[]
for row in rows:
 if row['path'].endswith('.receipt.json'):
  v=json.loads((R/row['path']).read_text());receipts.append({'path':row['path'],'exit':v.get('exit'),'sha256':row['sha256'],'killed':v.get('killed')})
terminal='terminal_manifest.receipt.json';v=json.loads((R/terminal).read_text());receipts.append({'path':terminal,'exit':v.get('exit'),'sha256':sha(R/terminal),'killed':v.get('killed')})
prev='0'*64;events=[]
for i,line in enumerate((R/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=hashlib.sha256(line).hexdigest();events.append(e)
assert sum(e['event']=='attempt' for e in events)==3
assert sum(e['event']=='success' for e in events)==0
record={'utc':now,'targets':[323710,323059],'review_lane':str(R),'manifest_count':len(rows),'manifest_mismatches':[],'frozen_bindings':len(f),'frozen_mismatches':[],'frozen_after':after,'receipts':receipts,'receipt_count':len(receipts),'receipt_exit_counts':dict(collections.Counter(str(x['exit']) for x in receipts)),'guard_chain_verified':True,'guard_last_sha256':prev,'guard_events':events,'actual_GET_hops':3,'successful_new_primary_bodies':0,'search_actual_calls':1,'search_query_strings':3,'full_search_response_sha256':sha(R/'search1-response.json'),'review_sha256':sha(R/'REVIEW.md'),'proof_sha256':sha(R/'PROOFS.md'),'independent_gates':json.loads((R/'keyedreview.json').read_text()),'root_dispositions':{'323059':'PARK: ordinary/literal-v1 PASS, identified2013final/correction/significance unpaid after cookie-loop guard denial; no further retrieval or formal dispatch','323710':'Ordinary/literal-original PASS and provisional substantive-content PASS; authorize one focused new source-version/companion/current-prior review, not formal execution or acceptance'},'procedure':'Conservative network STOP after guard repeated-URL PolicyError. Three real hops, no fourth request sent, no budget excess. Preserve failed receipt and author late-family reconciliation HOLD. Independent early94scope comparison does not retroactively cure author timing. Sampling/native/writer limitations retained.','credit':0,'accepted_new':55,'target_new':60,'previous_accepted':39,'root_execution':'Documentary integrity/adjudication only, no mathematical programs or Lean execution'}
parent=P/'cover-ratio-regular-mis-source-parent-integration-sol-r1.json';save(parent,record)

old=ROOT/'inherited-denials-r433-intake.json';den=json.loads(old.read_text());den['utc']=now
url='https://link.springer.com/content/pdf/10.1007/s11083-012-9253-5.pdf'
den['blocked_keys']=sorted(set(den['blocked_keys']+['link.springer.com/content/pdf/10.1007/s11083-012-9253-5.pdf']))
den['blocked_artifacts']=sorted(set(den['blocked_artifacts']+['10.1007/s11083-012-9253-5','ilinca-kahn order30(2013)427-435 identified final maximal-independent-set paper']))
den['records'].append({'url':url,'reason':{'artifact':'Ilinca-Kahn identified2013 Order30,427-435 final, DOI10.1007/s11083-012-9253-5','actual_charged_hops':3,'body_obtained':False,'outcome':'Publisher303/302cookie redirects; guard rejected repeated article URL BEFORE fourth request; all subsequent network stopped'},'evidence':{'path':str(R/'guard-ledger.jsonl'),'sha256':sha(R/'guard-ledger.jsonl')}})
den['root_regular_mis_final_scope']='Identified Ilinca-Kahn2013 Order30,427-435 final DOI10.1007/s11083-012-9253-5 artifact-wide unavailable across all alternate hosts, queries, versions, mirrors, author/arxiv1202.4427 deliveries or caches. No cookie/TLS/login bypass, no retry. Already saved originalv1 only may be read where copied/authorized. No blanket prohibition on unrelated Springer work; do not copy/reuse this auth chain.'
denpath=ROOT/'inherited-denials-cover-mis-review-r1.json';save(denpath,den)

tree=ast.parse((ROOT/'prepare-two-reviews-20261108.py').read_text())
common=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
common=common.replace('Inherited denial union r432','Inherited latest denial union cover-mis-review-r1')
L.mkdir();origins={}
def cp(src,rel):
 dst=L/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(src)==sha(dst);origins[rel]={'path':str(src),'sha256':sha(src)}
base=P/'expanded-corpus-r420'
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json']:cp(base/name,name)
cp(denpath,'inherited-denials.json')
for name in ['REVIEW.md','PROOFS.md','GAP.md','keyedreview.json','scope-comparison.json','source-obligation-map.json','access-inventory.json','source-read-inventory.json','figure-inventory.json','search-inventory.json','resource-inventory.json','MANIFEST.json','search-plan1.json','search1-response.json','guard-ledger.jsonl']:
 cp(R/name,'inputs/review/'+name)
for name in ['ACTUALBRIEF.md','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','literal-provenance.json','results.json','early-history-audit.json','family-reconciliation.json','access-inventory.json','source-read-inventory.json','registry-navigation.json','search1-response.json','search2-response.json','search3-response.json','literal323710.jsonl']:
 cp(R/'inputs'/name,'inputs/author/'+name)
for name in ['cover.pdf','cover.txt','cover-companion.pdf','cover-companion.txt','cover-author.html','current-openai-contents.md','current-leanpool-index.txt','current-tau-index.txt','current-deepmind-proofs.md']:
 cp(R/'inputs/sources'/name,'inputs/sources/'+name)
for name in ['accepted55-routing.json','prior39-routing.json']:cp(R/'inputs'/name,'inputs/'+name)
cp(parent,'inputs/ROOT-INTEGRATION.json')
save(L/'INPUT-ORIGINS.json',origins)
save(L/'reservation.json',{'ids':[323710],'role':'Focused source-version, actual2017companion and bounded current-prior/significance comparison; no formal execution','accepted_new':55,'target_new':60,'credit':0})
rs=sha(L/'reservation.json');(L/'reservation.sha256').write_text(rs+'  reservation.json\n')
save(L/'search-budget.json',{'calls_used':0,'queries_used':0,'maximum_calls':2,'maximum_queries':6,'charged_before_call':True})
detail='''This is a NEW focused investigation of concrete unpaid323710 source/version/primary-comparison obligations. It is NOT a rerun of failed323059 delivery, exhausted author search, or a request for worldwide proof absence. Only target323710, fixed equal-320-vertex normalized cover-cost/first-cover ratio. Root preserves independent full ordinary/literal-original PASS and PROVISIONAL substantive-content PASS, no formal dispatch or acceptance. Do not redo an ordinary proof as the main deliverable; read existing full proof, independently challenge any newly relevant bridge.

O1: establish actual current version/correction status of A Tractable Variant of Cover Time, arxiv1206.6605. The already copied actualPDF has banner28Jun2012v1 but internal25July2018; copied currentauthorpage calls Preprint2012. Do not infer chronology or absence of final solely from metadata. A single independently selected not-already-acquired exact current arxiv landing/history or primary author correction record may resolve version identity. Do NOT refetch already cachedPDF merely to erase dates. If latest primary is still the exact savedv1 and no identified final/correction exists in checked primary record, report bounded source-version PASS with precise evidence, not an invented universal journal-final requirement or worldwideabsence. If a concrete different final/version is identified, obtain actual body once subject to guard and compare exactDefinition1.1/equation1/Conjecture5.4 and hypotheses. No arbitrary nearby-paper substitution.

O2: actual2017 final Hitting Times, Cover Cost, and the Wiener Index of a Tree, AgelosGeorgakopoulos/StephanWagner, JGraphTheory84(3)311-326,2017, sourcearxiv1302.3212v2 already cached. Finalbody NOT previously requested or denied in this case; identify DOI/delivery from actual authoritative navigation, do not invent URL/DOI. Obtain ONE independently selected actualfinal primary body, then compare the complete material relevant statements/proofs, conclusion/corrections and Figure3 as needed to the v2 bounded nonmatch. Existing v2 review fully reads intro,T4summation,Cor5firststep,treeidentities/T7/9/10proofs,Section5/Figures1-3; these concern CC/RC/treeorderings, not cc/CT maximal ratio. Figure3clique-path-star comparesverticeswithinonegraph, not equal-ordergraph ratio; do not assert complete subsumption without actual bridge. If finalbody unavailable, stop that ARTIFACT across all alternate delivery and give preciseHOLD, no refetch route. Do not confuse deniedMISfinal10.1007/s11083-012-9253-5 with this distinctJGTpaper; no blanketSpringerban and no reuseofdeniedauthchain.

O3: bounded targeted actual current primary or registry comparison for exactnormalized cover-cost/first-cover extremal conjecture and known lollipop/coupon theorem that might completely subsume the counterexample. Saved currentOpenAICONTENTS/LeanPool172byteumbrella/Taumetadata/DeepMindpolicy are navigation only, not complete proof inventories. No exactmatchingtheorem currentlyidentified; if searchfindsone, inspectactualtheorem ANDproof before relying. Budget max2 actualnativecalls6querystrings,8GET-HOPS total/perID, allplans precharged/fullresponses immediately saved. Distinct prior bodies can be inspected; no old failed artifact alternate delivery, no cachedsource/rootrefetch. Unknownworldwidepriority itself is not a concrete theorem hold; state limits honestly. Scientific prospective qualification can be bounded if no matching concrete prior identified, but no globalnoveltyclaim.

Significance: independentordinaryproof exactroot0 path64attachedK256320vertices, cc>3072,CT<7168=>ratio>3/7 vs endpointpath<3/8. Finiteness, Markovexcursions and conditionalduration/Tonelli proof paid. Familiar lollipop+coupon method is strongest adaptation concern, but only a full applicable primary theorem-to-target bridge supports routine exclusion. Maintain strongest opposingassessment, never smallness/toolfamiliarity/Leanburden alone. Finalcandidateonlyonefamily,94scopecomparisonalreadyboundedPASS; preserve historical author late-family timingHOLD. No priorprintedexactcounterexampleclaim absent authenticbody.

Review only, no mathematicalprograms or formalexecution. Deliver REVIEW.md/keyedreview.json O1/O2/O3, source-obligationmap with exact readdepth, independent objections/fullnewbridges/GAP, current access/figure/search/resource inventories, allactualreceiptsha manifest/frozenafter. If allprospectivegatesPASS supply dormant fullliteralLeanplan only; literalwalk/hitting/cover/costexpectation sourcebridges stillrequiredlater. Explicit PDFskillread via runner and direct display of OWNrenderedimages are allowed, record distinctUI evidence/missingnative telemetry. No PDFauthoring required. No peeraccess. No credit/dispatch/acceptance.'''
task='Focused323710 review in '+str(L)+'. ReservationSHA256 '+rs+'.\nPROTECTED ACTIVE PEERS cmdrr-five-three-formal-sol-r2 and shoe-pair-discrepancy-source-review-sol-r1: NO read/hash/glob/list/poll evenmetadata.\n'+common.replace('LANE',str(L)).replace('TARGET','323710')+'\nSPECIFIC SCOPE:\n'+detail
(L/'TASK.txt').write_text(task)
frozen={str(q):sha(q) for q in R.rglob('*') if q.is_file()}
frozen.update({str(q):sha(q) for q in (L/'inputs').rglob('*') if q.is_file()})
for name in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','model-policy-sol-only.json','inherited-denials.json','INPUT-ORIGINS.json','reservation.json','reservation.sha256','TASK.txt']:frozen[str(L/name)]=sha(L/name)
assert all(sha(Path(s))==v for s,v in frozen.items())
save(L/'frozen-inputs.json',frozen)
ready={'utc':now,'lane':str(L),'target':323710,'frozen_bindings':len(frozen),'reservation_sha256':rs,'task_sha256':sha(L/'TASK.txt'),'parent_integration':str(parent),'latest_denial_union':str(denpath),'accepted_new':55,'credit':0,'model':'gpt-6.1-sol','reasoning_effort':'high','service_tier':'default','network_limits':{'GET_hops':8,'search_calls':2,'query_strings':6}}
save(L/'ROOT-PREP.json',ready);save(ROOT/'cover-primary-comparison-r2-ready.json',ready)
print(json.dumps({'manifest_files_verified':len(rows),'frozen_verified':len(f),'receipt_counts':record['receipt_exit_counts'],'ready':ready}))
