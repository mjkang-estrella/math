"""Root documentary integrity, exact-public-result disposition and routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'split-decomposition-orthogonality-source-review-sol-r1'
# Extract only prior root verification definitions, never execute old integrations/preparations.
s=(ROOT/'intake-eps-staircase-prepare-r485-r486.py').read_text();prefix=s[:s.index('\neps=verify(')]
changes={
 "files=m['files'];assert isinstance(files,dict) and len(files)==nfiles":"files={x['path']:x for x in m['files']};assert len(files)==len(m['files'])==nfiles",
 "ex=m.get('terminal_exclusions',m.get('precise_terminal_noncircular_exclusions'))":"ex=m['terminal_noncircular_exclusions']",
 "terminal_manifest.receipt.json":"terminalmanifest28.receipt.json",
 "terminal_manifest.output.txt":"terminalmanifest28.output.txt",
 "response=read(a/f'search-response-{i}.json')":"response=read(a/f'search-response{i}.json')",
 "assert set(gates)=={str(target)} and gates[str(target)]['accepted_credit']==0 and not gates[str(target)]['qualified_survivor']":"assert set(gates)=={str(target)} and gates[str(target)]['credit']==0 and gates[str(target)]['recommendation']=='EXCLUDE_PUBLIC_RESULT'",
}
for old,new in changes.items():assert old in prefix,old;prefix=prefix.replace(old,new)
ns={'__file__':str(__file__)};exec(compile(prefix,str(ROOT/'intake-eps-staircase-prepare-r485-r486.py')+'#verifier-only','exec'),ns)
record=ns['verify']('split-decomposition-orthogonality-source-review-sol-r1',382572,122,27,'split-orthogonality-review-r1-ready.json','review.json',dict(attempt=4,success=3,unavailable=1),2,6)
sha=ns['sha'];read=ns['read'];save=ns['save'];now=datetime.datetime.now(datetime.timezone.utc).isoformat()
g=read(A/'review.json')['382572'];assert g['gates']['prior']=='EXACT_PUBLIC_KIM_0705_0167V1_THEOREM6_8'
assert sha(A/'sources/kim-duality.pdf')=='0732c848f4504cd453699f516a20cb1e2500b4b4a31e4487bd1f87395009e9e7'
assert sha(A/'sources/kim-matrices.pdf')=='9dee23367ce8a71dafccc25089cdad84821c70741000b7d63c965c117a99c7b6'
assert read(A/'finalget17.receipt.json')['exit']==1
events=[json.loads(x) for x in (A/'guard-ledger.jsonl').read_text().splitlines()];failure=[e for e in events if e['event']=='unavailable'];assert len(failure)==1 and failure[0]['status']==503
record.update(root_disposition='EXCLUDE_EXACT_PUBLIC_KIM_2007_THEOREM6_8',
 ordinary='IndependentfullordinaryPASS exactsource-boundglobaltilde-spaceequality andbothorientationpairs forallindices includingzeros,boundarycases. Independentcheckpointprecedesauthorproof. No root mathematical solving/programs/formalexecution.',
 prior='ActualJoohyungKim A duality between pairs of split decompositions for a Q-polynomial distance-regular graph arXiv0705.0167v1 1May2007 Theorems1.1/6.8 andcompleteapplicableproof/Lemma6.7 global-equality bridge readbyreviewer. Rootpersonallyreadcachedactualtheorem/proofandlaterrestatement as documentarycomparison. OriginalRemark8.2 mapsactualsourceassumption/orderingtobroaderQ-polynomial setup,allsourceindexdefinitionsretained. Exactpublicresult,noliteralendpointleftunpaid.',
 public_counterpart=dict(title='A duality between pairs of split decompositions for a Q-polynomial distance-regular graph',author='Joohyung Kim',arxiv='0705.0167v1',date='2007-05-01',theorem='Theorems1.1/6.8, Lemma6.7',pdf_sha256=sha(A/'sources/kim-duality.pdf'),matrices_restatement='Distinct0710.4383v1Theorem3.23 cites reference12Theorem4.8 versus downloadeddualityv1Theorem6.8; numbering/editiondifferencepreserved,not silentlyequated.'),
 significance='RootadoptsEXCLUDE_PUBLIC_RESULT0. Separatelyreviewedcomplete sourceSection7/Lemmas10.3/11.3/11.4-to-globaltarget routinebridge supports0,butdecisiveexactpublicTheorem6.8stronger. Original2006Conj13.6/openlabelandmissingglobalbridgepositivecasepreserved;notshortness/inventedearlierprintedcorollary.',
 source='LiteralUnderAssumptioncontext recoveredasAssumption8.1,Section7D>=3,Remark8.2idempotentorder;definedspaces supplyr,srange. Originalv1sourcePASS,final/correctionunqualified. OriginallaterinstitutionalcopyHTTP503 meansentiremath0608694/finalDOI10.1016/j.ejc.2008.07.011workALLnewdeliveryblocked. DistinctKim0705.0167and0710.4383notblocked;neitherjournaleditionclaimedbyteidentical/read.2009matricespaperdistinctnotoriginalor0710-yearconflation.',
 process='122manifestfiles27frozenverified; actualfourGEThops threepayloads(twoKimPDF,metadataHTML),oneHTTP503,noredirect/retry. Twochargedsearchessixqueries/fullresponsesverified. OriginalsourceincidentalhitsafterfailureinKimsearchnotusedforrecovery. Materialdocumentarydisplaytruncationsrecovered,targetedreadscopepreserved;no rootprotectedexternalpathfollow,nouniversalresource/accessassurance. Allinheritedblocksretained,registryrootsnotreconstructed.',
 family='Trusted57+39boundedscopenonmatch,notupstreamcertificateaudit. Allfourorientation/helper/parametervariantsonefamily0;publicproof/formalizationnoextraoutcome.',
 formal='Notrun/notrouted,nocostlyformalplanoracceptance.57/60newbeyond39prior96totalunchanged.')
delta='Completed382572independentfullsourceordinaryPASS includingglobaltildeequality/bothorientationpairs/allindices. ROOTEXCLUDEEXACTPUBLIC Kim A duality between pairs of split decompositions for a Q-polynomial distance-regular graph 0705.0167v1(1May2007)Theorems1.1/6.8 andLemma6.7fullproofread,broaderQ-polynomialassumptions/sourceRemark8.2bridge. Distinct0710.4383v1KimMatricesTheorem3.23restatesexactclaim,citationTheorem4.8versusdownloadeddualityv1Theorem6.8editionnumberdifferencepreserved,nofinaljournalequivalence. Alsocompleteordinaryroutinebridgepaid,notshortness. NEWENTIRE ItoTerwilliger Distance-regular graphs and the q-tetrahedron algebra originalmath0608694/finalDOI10.1016/j.ejc.2008.07.011/institutional13248ALLNEWdeliveryunavailable afterinstitutionalSC-PR-ITO-T-682.pdfHTTP503;cachedpredenialv1only,distinctKimworksnotdenied.122files27frozen4GET3payloads1HTTP5032search6queriesverified,nofreshregistryheads/deepupstreamauditclaim. Noformaldispatch/credit,57/60unchanged.'
den=read(ROOT/'inherited-denials-r494.json');den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure[0]['url_key'],'doi.org/10.1016/j.ejc.2008.07.011'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'math/0608694','0608694','10.1016/j.ejc.2008.07.011','distance-regular graphs and the q-tetrahedron algebra','sc-pr-ito-t-682.pdf'})
den['records'].append(dict(url=failure[0]['url'],reason=dict(status='HTTP503',artifact='ItoTerwilliger Distance-regular graphs and the q-tetrahedron algebra originalmath0608694/finalDOI10.1016/j.ejc.2008.07.011/institutional13248',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retries/identity correction/indirect recovery. Explicitalready-suppliedpre-failurev1only,notfinalequivalence. DistinctKim0705.0167and0710.4383notdenied.'),evidence=dict(path=str(A/'review.json'),sha256=sha(A/'review.json'),guard_sha256=sha(A/'guard-ledger.jsonl'),receipt_sha256=sha(A/'finalget17.receipt.json'))))
den['root_split_orthogonality382572_review_scope']=delta;denpath=ROOT/'inherited-denials-r495.json'
# All verification precedes integrations and new discovery preparation.
save(P/'split-decomposition-orthogonality-source-parent-integration-sol-r1.json',record);save(denpath,den)
config=read(ROOT/'r488-config.json');config.update(number=489,protected_peers=['expanded-corpus-r488','cubical-zigzag-source-review-sol-r1'],peer_routing_files=['selection-routing-r488.json','selection-routing-cubical-zigzag-review-r1.json'],denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
config['completed_discovery_numbers']=sorted(set(config['completed_discovery_numbers'])|{487})
config['excluded_ids']=sorted(set(config['excluded_ids'])|{378413,382572})
config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/math/0405279','https://arxiv.org/abs/1509.03754','https://arxiv.org/abs/math/0608694','https://arxiv.org/abs/0705.0167','https://arxiv.org/abs/0710.4383'})
config['steering']+='\n'+den['root_r487_scope']+'\n'+delta+'\n';save(ROOT/'r489-config.json',config)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json');forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for name in allow:
 rel=Path(name).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'split-orthogonality-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r489',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(files=122,frozen=27,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready,accepted_new=57,credit=0)))
