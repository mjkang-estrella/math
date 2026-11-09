from research import *
ledger=json.loads((L/'administrative'/'ledger.json').read_text());prior=json.loads((L/'administrative'/'prior-campaign-context.json').read_text())
save('administrative-reading.json',{'accepted_count':ledger['accepted_count'],'total':ledger['total_accepted_count'],'next':ledger['next_global_outcome_number'],'accepted_titles':[x.get('title') for x in ledger['accepted']],'prior_accepted_titles':[x.get('title') for x in prior['accepted']],'scope':'administrative snapshots only, not immutable-source bindings'})
save('failures.json',[
 {'kind':'full-proof-unavailable','url':'https://apcz.umk.pl/TMNA/article/view/47721/37305','result':'200 redirect to subscription page; no Theorem4.10 body; no restricted-file guessing or bypass'},
 {'kind':'challenge','url':'https://www.google.com/search?q=%22operator+of+center+of+distances%22','result':'200 challenge HTML; stopped; no retry, execution, proxy or browser'},
 {'kind':'dependency','script':'search.py initial version','result':'ModuleNotFoundError: bs4; preserved here, replaced parsing with standard-library regex'},
 {'kind':'wrong-paper','path':'primary/centers-2025.pdf','result':'arXiv2502.06504 was a noisy search hit about RR Lyrae, NOT mathematics; retained, excluded from evidence'},
 {'kind':'nonresponsive','path':'primary/bing-tmna.html','result':'search results for running shoes; does not constitute literature coverage'},
 {'kind':'broad-index','result':'initial rg inventory and later local filename search overinclusive/truncated; no conclusions inferred from truncation'},
 {'kind':'mathematical-failure','result':'aligned holes lose distance1 for C={0,1,3/2,3}; no inference of nonrealizability'},
 {'kind':'mathematical-failure','result':'separated finite gadget diameters diverge with infinitely many complement gaps'},
 {'kind':'parked','result':'GitHub API/raw/codeload/diff/patch, ScienceDirect, prior Google challenge routes and inaccessible historical intervals not revisited; no current registry-head certification'}])
records=[json.loads(x) for x in (L/'bindings.jsonl').read_text().splitlines()]
retrieval=[json.loads(x) for x in (L/'retrieval.jsonl').read_text().splitlines()]
textmap=[]
for pdf,txt in [('survey.pdf','survey.txt'),('centers-new.pdf','centers-new.txt'),('cardinality.pdf','cardinality.txt'),('up23.pdf','up23.txt'),('tmna-preview.html','tmna-preview.txt')]:
 textmap.append({'pdf':'primary/'+pdf,'pdf_sha256':sha(L/'primary'/pdf),'text':'primary/'+txt,'text_sha256':sha(L/'primary'/txt),'extractor':'pdftotext -layout; every input frozen before extraction and text frozen before scientific reading'})
save('primary-text-bindings.json',textmap)
(L/'RUN.md').write_text('''# Capped local replay

Run from this lane. Do not rerun retrieval scripts on parked/denied routes.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py
```

verify.py independently checks manifest inventory, all scientific originals and frozen copies, then replays checks.py and intervals.py as children within the same guarded group and checks deterministic output hashes. It writes verification-receipt.json, excluded from the manifest. Limits are fixed512MiB AS/groupRSS,CPU210s,wall230s,threads1, with no cap raises. finalize.py writes the manifest; verification is a separate invocation after all writes. The manifest excludes only itself and the receipt. Scientific non-resolution and missing TMNA4.10 body remain explicit even when integrity verification passes.
''')
save('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'guard':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','limits':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'threads':1,'cap_raises':False},'scientific_bindings_file':'bindings.jsonl','binding_records':len(records),'retrieval':retrieval,'before_read_freeze':'new downloads and selected historical files copied to content-addressed lane paths and both digests verified before scientific reads; all originals/copies checked again by separate verifier','administrative':'snapshot only','source_scope':'question passages and named proof excerpts only; freezing a file does not assert its full body was read','main_missing_body':'TMNA Theorem4.10','no_new_theorem_claim':True,'credit':0,'counts':[9,39,40]})
save('source-bindings.json',{'bindings':'bindings.jsonl','pdf_text_bindings':'text-bindings.jsonl','fresh_target_pdf':{'path':'primary/survey.pdf','sha256':sha(L/'primary'/'survey.pdf')},'preview_only':{'path':'primary/tmna-preview.html','sha256':sha(L/'primary'/'tmna-preview.html')},'note':'tmna-preview.html contains a PDF despite filename; centers-2025.pdf is excluded as nonmathematical; frozen historical references reused without recursively copying evidence'})
files={str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
save('manifest.json',{'excludes':['manifest.json','verification-receipt.json'],'files':files})
print('Final files written; run separate verifier now.',len(files))
