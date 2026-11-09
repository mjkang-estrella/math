"""Root documentary integrity/disposition and metadata-only routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'cyclic-unit-fixed-sums-source-review-sol-r1'
# Reuse only the completed root verifier definitions; never execute prior mutations.
source=(ROOT/'intake-eps-staircase-prepare-r485-r486.py').read_text();prefix=source[:source.index("\neps=verify(")]
old="response=read(a/f'search-response-{i}.json');assert isinstance(response,str) and len(response)>1000"
new="response=read(a/('search-one-response.json' if i==1 else 'search-two-response.json'));assert isinstance(response,str) and len(response)>1000"
assert old in prefix;prefix=prefix.replace(old,new)
old="assert set(gates)=={str(target)} and gates[str(target)]['accepted_credit']==0 and not gates[str(target)]['qualified_survivor']"
new="assert set(gates)=={str(target)} and gates[str(target)]['gates']['acceptance']['credit']==0 and not gates[str(target)]['gates']['acceptance']['accepted']"
assert old in prefix;prefix=prefix.replace(old,new)
ns={'__file__':str(__file__)};exec(compile(prefix,str(ROOT/'intake-eps-staircase-prepare-r485-r486.py')+'#verifier-definitions-only','exec'),ns)
record=ns['verify']('cyclic-unit-fixed-sums-source-review-sol-r1',316244,99,24,'unit-sums-review-r1-ready.json','keyedreview.json',dict(attempt=2,redirect=1,success=1),2,6)
sha=ns['sha'];read=ns['read'];save=ns['save'];now=datetime.datetime.now(datetime.timezone.utc).isoformat()
payload=A/'sources/complete-sums-final.html'
assert payload.stat().st_size==2655 and b'Redirecting' in payload.read_bytes()
assert read(A/'get_final_body.receipt.json')['exit']==0
assert read(A/'scope39_and_searchtwo.receipt.json')['exit']==1
assert read(A/'new-unavailability.json')['scientific_body_available'] is False
record.update(root_disposition='EXCLUDE_EVEN_MODULUS_DOMAIN_CORRECTION_ZERO_CREDIT',
 ordinary='Independent full literal/cachedv1 ordinary PASS for n16,eightunits,k4,size/ceiling/nonemptyfour-distinctsubsets/parityquotient/cardinality; powersoftwoextension onefamily. Root records reviewer findings and scientific disposition,no root proof solving or mathematical computation.',
 source='Root personally read cachedoriginal pp1-2 as documentary comparison: EXACT kdistinct sums and separately variablelength union; printedConj1.2 generaln,coprimality,non-strictthreshold,ceiling,explicitreset afterprimeparagraph. No hiddenprime/odd requirement authenticated by reviewer. v1 fidelityPASS retained,not finaljournal equivalence. CorpusOlsonreference association corrected separately: introduction attributes primevariablelengththeorem,not compositefixedlengthConj1.2.',
 significance='Root adopts zero-credit even-modulus domain-correction exclusion. Complete fixedlength unit-sum parity obstruction is independent of a specialconfiguration beyond feasiblehypotheses; source extension from prime/variablelength scope missed paritydomain. Strongest contrarycase is genuine full printedv1 conjecture negation withsubstantialnonemptyunitset/infinitefamily; shortness or sourceconjecturelabel alone notbasis. No claim earlierexactprintedrefutation or authenticatedroutine-priorbridge; no correctedodd-modulus theorem claimed.',
 prior='Boundedtwo-searchsix-query investigation did not authenticate a matching prior theorem/proof; no globalnoveltyclearance. Identifiedactual2008JCTAfinal DOI10.1016/j.jcta.2007.12.007/PIIS009731650800006X unread afterredirectHTML,entireworknewdeliveryunavailable. Do not carry metadataabsence as proof of nofinal; exactfinalwasidentified. Specificfinalscope/correctionHOLD remains,not a reason togrant credit to domaincorrection.',
 family='Trusted57+39boundedscopenonmatch; alleven-modulus/units/fixedlength/powersoftwovariants onefamily,noseparatecredit.',
 process='99manifestfiles24frozenverified; actualtwoHTTPSGEThops/one2655byteRedirectingHTML/one302,nounauthorizedrecoveryreported. Twochargednative searches,sixqueries; fullactualresponses saved. Preservedoneouterexit1scope39KeyError beforesearch2precharge,thenfreshdocumentaryrepair; noreset/refund. Imagepayloadtruncation recoveredfromsame renderedbytes. Root verifies hashes/ledgers/receiptcaps,not universal access/resource certification; native/transient/writer/supervisorpeaksunknown. All reportedmidrunupdates savedwithoutfrozenwrites.',
 formal='Noformalexecution/dispatch/costlyformalplan; frozenauthorplannotactivated. Zeroacceptedcredit,57/60beyond39prior96total unchanged.')
delta='Completed316244independentordinaryandv1PASS,ROOTEXCLUDEeven-modulusdomaincorrection0. Exactfixedlengthdistinctsumdefinitionseparatefromarbitrarylengthcompleteness,sourceprintsalln/coprmiality/noprimeoroddreset; eightunitsn16/k4paritycertificatefullypaid,oneevenmodulusfamily. CorpusOlsonreferenceassociatedwithprecedingprimevariablelengththeorem,notConj1.2. Strongpositivefullprintedconjecturenegationretained,butunavoidableparitydomainobstruction supportsdomaincorrectionexclusion,notshortness/noearlierexactpriorclaim/nooddtheorem. NEW entireHamidouneLladoSerra On complete subsets of the cyclic group original0704.0541/JCTA115(7)(2008)1279-1285 DOI10.1016/j.jcta.2007.12.007/PIIS009731650800006X ALLNEWdeliveryunavailable after2655byteRedirectingHTML;frozenpredenialv1onlynotfinalequivalence.99files24frozen2HTTPSGET1nonpaper1redirect2search6queriesverified;documentaryKeyError/parsertruncationspreserved/repaired,nofrozen/guard/counterreset. Noformaldispatch/credit;57/60,96totalunchanged.'
den=read(ROOT/'inherited-denials-r490.json');den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'doi.org/10.1016/j.jcta.2007.12.007','linkinghub.elsevier.com/retrieve/pii/S009731650800006X'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'0704.0541','10.1016/j.jcta.2007.12.007','s009731650800006x','on complete subsets of the cyclic group'})
den['records'].append(dict(url='https://doi.org/10.1016/j.jcta.2007.12.007',reason=dict(status='DOI302linkinghub2002655byteRedirectingHTMLnotpaper',artifact='HamidouneLladoSerra On complete subsets of the cyclic group JCTA115(7)(2008)1279-1285/original0704.0541',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retries/identity correction/indirect recovery. Explicitalready-supplied pre-failurev1 only,notfinalequivalence. Distinctother subset-sum papers notblanketdenied.'),evidence=dict(path=str(A/'new-unavailability.json'),sha256=sha(A/'new-unavailability.json'),guard_sha256=sha(A/'guard-ledger.jsonl'),payload_sha256=sha(payload))))
den['root_unit_sums316244_review_scope']=delta
denpath=ROOT/'inherited-denials-r491.json'
# All verification precedes these root-only documentary writes.
save(P/'cyclic-unit-fixed-sums-source-parent-integration-sol-r1.json',record);save(denpath,den)
config=read(ROOT/'r486-config.json');config.update(number=487,protected_peers=['expanded-corpus-r485','expanded-corpus-r486'],peer_routing_files=['selection-routing-r485.json','selection-routing-r486.json'],denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
config['steering']+='\n'+delta+'\n';save(ROOT/'r487-config.json',config)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'unit-sums-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r487',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=99,frozen=24,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready,accepted_new=57,credit=0)))
