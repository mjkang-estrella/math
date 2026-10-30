from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
before=json.loads((p/'before-hashes.json').read_text());after=[]
for r in before['files']:
 orig=Path(r['path']);cp=p/'private-input'/orig.relative_to(Path(before['files'][0]['path']).parent)
 a=sha(orig);b=sha(cp)
 assert a==b==r['sha256'],str(orig)
 after.append({'path':str(orig),'sha256_before':r['sha256'],'sha256_after':a,'private_after':b})
manifests=[]
for name in ['scientific-freeze.json','finalmanifest.json']:
 records=json.loads((p/'private-input'/name).read_text())['records']
 for r in records:
  f=p/'private-input'/r['path'];assert f.stat().st_size==r['bytes'] and sha(f)==r['sha256']
 manifests.append({'file':name,'verified':len(records),'sha256':sha(p/'private-input'/name)})
(p/'after-hashes.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all94_unchanged':True,'candidate_manifest_checks':manifests,'files':after},indent=2))
# Preserve short exact passages with source hashes, independent of the root excerpts.
evidence=[]
for name,anchors in [('dsbs-clean.txt',['I-C Problem Formulation','For \\alpha\\in[-\\infty,0) , define','Conjecture 1 .','Proposition 1 (','IV-A Converse','Appendix C Proof']),('companion-clean.txt',['Theorem 3 (Rényi Resolvability Rates)','Statement 2 for q\\in(1,\\infty]']),('gray.html.txt',['Theorem 2'])]:
 f=p/'private-input/sources'/name;t=f.read_text();parts=[]
 for anchor in anchors:
  pos=t.find(anchor);parts.append({'anchor':anchor,'position':pos,'excerpt':t[pos:pos+8000] if pos>=0 else 'anchor not found; full retained source consulted'})
 evidence.append({'file':str(f.relative_to(p)),'sha256':sha(f),'passages':parts})
(p/'source-evidence.json').write_text(json.dumps(evidence,indent=2,ensure_ascii=False))
lib=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib')
files=['InformationTheory/KullbackLeibler/Basic.lean','InformationTheory/KullbackLeibler/ChainRule.lean','InformationTheory/KullbackLeibler/DataProcessing.lean','Probability/ProbabilityMassFunction/Basic.lean','Probability/ProbabilityMassFunction/Constructions.lean','Analysis/SpecialFunctions/BinaryEntropy.lean','Analysis/Convex/Caratheodory.lean']
(p/'library-evidence.json').write_text(json.dumps([{'path':str(lib/x),'sha256':sha(lib/x)} for x in files],indent=2))
failures=[{'action':'initial guarded copy setup','failure':'ValueError: absolute input path not relative to relative base path','repair':'resolve base before relative_to; initial attempt created only the designated lane directory','guard_exit':1,'peak_sampled_group_rss':10264576}, {'action':'first independent rational check','failure':'AssertionError on exact posterior marginal; integer zero divisions introduced Python floating zero','repair':'convert every processor entry, including zeros, to Fraction before arithmetic; independent check then passed','guard_exit':1,'peak_sampled_group_rss':31858688}, {'action':'review draft branch monotonicity argument','failure':'draft incorrectly asserted F_qq positive throughout entire branch; false near q=1/2','repair':'before finalization replaced with exact atanh sign argument; candidate only requires local positive second derivative and is unaffected'}, {'action':'native bounded reads','failure':'several combined ledger/context/freeze/source/rg outputs truncated; one unbounded cache-directory listing produced excessive output','repair':'re-read mathematical proof and relevant actual-body sections with bounded slices; no claim of exhaustive unrelated body or global-history reading; no state mutation'}, {'action':'publisher-body access','failure':'both IEEE stamp requests returned418','repair':'stop; no retry/bypass; VoR comparison remains HOLD'}]
provenance={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'independent solo preliminary review','lane':str(p),'candidate_root':str(Path(before['files'][0]['path']).parent),'frozen_originals':94,'candidate_scientific_records':91,'candidate_manifest_records':92,'review_proof_sha256':sha(p/'private-input/PROOF.md'),'private_replay_checks_json_byte_identical':sha(p/'private-input/checks.json')==next(r['sha256'] for r in before['files'] if Path(r['path']).name=='checks.json'),'failures_and_deviations':failures,'commands_policy':'All Python/helper/retrieval/hash/extraction/edit commands run through unchanged supplied helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1; native reads and apply_patch also used. No cap raises. Guard AS/group RSS512MiB CPU210 wall230 nominal40ms. Sampled RSS is not continuous peak certification.','helper_guard_sha256':sha(p.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'guard_success_samples_bytes':{'input_copy':19308544,'live_primary_metadata':24440832,'publisher_access':24002560,'independent_check':17141760,'private_candidate_replay':17248256},'source_receipts':['live-sources/http.json','live-sources/vor-access.json','live-sources/main-crossref-receipt.json'],'no_lean_build':True,'no_children':True,'no_git':True,'no_browser':True,'no_external_messages_uploads_or_public_actions':True,'no_shared_or_count_edits':True,'verdicts':{'SOURCE':'PASS arXiv target; published-body coverage incomplete','MATH':'PASS ordinary proof using attributed nontrivial input','SUBSTANTIVE':'qualified positive preliminary assessment; adaptation objection retained','NOVELTY':'HOLD specific VoR and bounded prior coverage limits','FORMAL_FEASIBILITY':'possible but substantial missing infrastructure; no certificate'},'input_freeze_scope':'94 immutable candidate files only; no snapshot/hash freeze of concurrently changing NEXT; candidate frozen context snapshot copied as part of original input','counts_observed':{'additional':9,'total':39,'next':40}}
(p/'provenance.json').write_text(json.dumps(provenance,indent=2))
print('PASS: all94 original/private files unchanged; scientific91 and manifest92 independently verified')
