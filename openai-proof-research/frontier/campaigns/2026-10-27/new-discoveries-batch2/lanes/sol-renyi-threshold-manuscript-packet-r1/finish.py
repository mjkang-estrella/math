import json,hashlib,zipfile,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
receipt=json.loads((R/'rebuild-final/receipt.json').read_text())
assert receipt['paper_sha256']==sha(R/'paper.pdf')
assert receipt['packet_sha256']==sha(R/'packet.zip')
assert (R/'paper.pdf').read_bytes()==(R/'rebuild-final/paper.pdf').read_bytes()
assert (R/'packet.zip').read_bytes()==(R/'rebuild-final/packet.zip').read_bytes()
freeze=json.loads((R/'freeze-before.json').read_text())
for n,h in freeze['files'].items():assert sha(Path(freeze['root'])/n)==h,n
for n,h in json.loads((R/'consulted-before.json').read_text()).items():
 p=R.parent/n if not n.startswith('../') else R.parent.parent/n[3:]
 assert sha(p)==h,n
for p in json.loads((R/'packet/component/dependency-hashes.json').read_text()):assert sha(Path(p['path']))==p['sha256']
for n,h in json.loads((R/'packet/manifest.json').read_text()).items():
 assert sha(R/'packet'/n)==h,n
 assert sha(R/'extracted-final'/n)==h,n
for n in range(1,5):assert (R/f'final-page-{n}.png').is_file()
audit=json.loads((R/'rebuild-final/replay/replay-receipt.json').read_text())
assert audit['declaration_count']==104 and len(audit['modules'])==11
assert len({d['name'] for d in audit['declarations']})==104
assert {'Renyi.every_order_counterexample','Renyi.not_source_threshold'}<={d['name'] for d in audit['declarations']}
hashes={n:sha(R/n) for n in ['paper.pdf','packet.zip','packet/manifest.json','rebuild-final/receipt.json','rebuild-final/replay/replay-receipt.json','replay-fresh/replay-receipt.json']}
proof=next(d for d in audit['declarations'] if d['name']=='Renyi.every_order_counterexample')
prov={'status':'DELIVERED_FOR_INDEPENDENT_FINAL_REVIEW','credit':0,'independent_final_review':'pending','root_acceptance':'pending','source_component_sha256':'ade57965f51e871329be7e62c84b6b8f6c694206b0f20d4bddb1a6bf377ef32d','hashes':hashes,'byte_identical_extracted_rebuild':True,'fresh_full_replay':receipt,'all_frozen_sources_unchanged':True,'all_eight_inherited_math_modules_unchanged':True,'upstream_dependency_companions_rehashed_after':True,'actual_declarations_audited':104,'mathematical_modules':11,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'visual_review':{'pages':4,'all_pages_inspected':True,'clipping_overlap_missing_glyphs':False,'render_log':'render-delivery.log'},'toolchain':'packet/toolchain.json','formal_pins':'packet/component/pins.json','resource_guards_unchanged':True,'limitations':['Bounded adopted prior investigation, not a new current registry refresh or worldwide priority proof.','PDF skill Node marker could not initialize under fixed helper memory cap; failure preserved; no cap raised.','Renderer dependencies external, pinned and checked; font assets included.','Original packet-seal manifest accidentally excluded nested manifests; strict packer rejected it. Corrected source sealing includes them; exact-set check retained.','Rejected multi-file apply_patch made no changes; corrected patch applied separately.'],'final_review_freeze':'final-review-freeze-manifest.json'}
(R/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
lines=['# Rényi threshold manuscript and deterministic packet','',
 'Delivered within the assigned lane for independent final review. Credit zero; root acceptance and later bounded freshness refresh remain pending. No shared edits, git commands, children, browser tabs, account actions, external messages, posts, publishing or uploads were used.','',
 '## Result and scope','',
 'The four-page manuscript proves that for every real 0<p<1 a finite normalized truncated exponential has a strictly larger iid positive-sum entropy increment than the rate-one exponential. It preserves the literal density, convolution tent, J/Ja deficit, DCT majorant (2u)^p, input denominator and c^p, and strict logarithmic comparison. The midpoint p=(1+p0)/2 negates SourceThresholdConsequence. The target is Fu–Li2510.09206v3 printed p2 after(1.2), not Shannon Conjecture1.1. No optimizer, cube or all-rate theorem is claimed. Authorship is Research manuscript, following existing campaign papers.','',
 '## Verification','',
 'Fresh final ZIP extraction rebuilt paper.pdf and packet.zip byte-identically. Its isolated source-only replay passed all 11 modules and all 104 actual declarations, including generated helpers. FullAudit imports all actual module bodies; declaration type, origin, transitive axioms and unsafe/partial/axiom flags were checked. Only propext, Classical.choice and Quot.sound occur. The pinned compiler, Mathlib and eight auxiliary pins and exact upstream .olean/private/server companion set were verified. Companions were rehashed after the final replay. No own compiled artifacts occur in the ZIP.','',
 'Frozen input hashes match before and after; all eight inherited mathematical modules remain byte-identical. All four final pages were rendered with Poppler and individually visually inspected: no clipping, overlap, missing glyphs or box warnings. ReportLab emits no TeX boxes; its actual build logs are clean. Exact renderer, fonts, zlib and toolchain versions are bound in packet/toolchain.json and checked by verify.py.','',
 '## Reproduction and receipts','',
 'Extract packet.zip into an empty source directory. With the pinned external renderer dependencies and immutable formal installation available, run `python3 component/helper_guard.py python3 verify.py /absolute/new/output-directory`. The output must not exist. Generated outputs stay outside the source tree. The verifier checks exact source file membership and hashes, renderer pins and fonts, rebuilds both artifacts, then performs the full isolated Lean replay. README.md documents the external dependency contract.','',
 'Final rebuild receipt: rebuild-final/receipt.json. Exhaustive declaration audit and resource receipts: rebuild-final/replay/replay-receipt.json and rebuild-final/replay/logs/. Earlier fresh replay: replay-fresh/. Full source/evidence manifest: packet/manifest.json. Final review freeze: final-review-freeze-manifest.json.','',
 '## Qualifications and failures','',
 'Adopted bounded novelty and attribution limits are preserved in the paper and packet/SOURCE-ATTRIBUTION.md, with full preliminary, r2 and registry-r3 reviews. No fresh worldwide or terminal registry investigation is claimed. The 51 historical context-source hash mismatches, recovered exact atoms, selective baseline semantic coverage and earlier inherited failures remain disclosed. Bulk survey inventories were not copied.','',
 'The PDF skill marker failed in Node initialization under the fixed 512MiB AS guard, including existing alternate runtimes; it was not successfully completed. Memory caps were never increased. Earlier missing-renderer and font-path failures and a strict source-manifest rejection are retained. The manifest exclusion bug was corrected in the source sealer; exact membership checks were preserved. No mathematical or visual PASS is inferred from the failed marker.','',
 '## SHA256','']
lines += [f'- {n}: `{h}`' for n,h in hashes.items()]
(R/'FINAL-RESULT.md').write_text('\n'.join(lines)+'\n')
targets=['paper.pdf','packet.zip','provenance.json','FINAL-RESULT.md','rebuild-final/receipt.json','rebuild-final/replay/replay-receipt.json']
(R/'SHA256SUMS').write_text(''.join(sha(R/n)+'  '+n+'\n' for n in targets))
files={}
for p in R.rglob('*'):
 if not p.is_file():continue
 n=p.relative_to(R).as_posix()
 if n.startswith(('vendor/','extracted-source/','extracted-final/')) or '__pycache__' in n:continue
 if p.suffix in ['.olean','.ilean','.ir','.sig'] or '.olean.' in n:continue
 if n in ['final-review-freeze-manifest.json','finish.log']:continue
 files[n]=sha(p)
(R/'final-review-freeze-manifest.json').write_text(json.dumps({'status':'FROZEN_FOR_INDEPENDENT_REVIEW_NOT_ACCEPTED','files':files},indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':prov['status'],'hashes':hashes,'frozen_paths':len(files)},indent=2))
