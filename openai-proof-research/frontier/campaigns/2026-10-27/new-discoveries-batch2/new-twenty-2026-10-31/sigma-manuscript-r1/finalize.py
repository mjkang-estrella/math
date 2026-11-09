from pathlib import Path
import json,hashlib,zipfile,datetime,os
R=Path(__file__).resolve().parent;B=R.parent

def h(p):
 q=hashlib.sha256()
 with p.open('rb') as f:
  for s in iter(lambda:f.read(1048576),b''):q.update(s)
 return q.hexdigest()
def out(n,o): (R/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
res=json.loads((R/'final-extraction/replay-receipts/result.json').read_text());assert res['status']=='PASS'
# Rescan the complete named trees, so added/deleted files are detected too.
names=['sigma-formal-r2','expanded-corpus-r60','sigma-source-review-r1','sigma-fidelity-novelty-review-r1','sigma-novelty-focused-r2','sigma-novelty-root-adjudication-r1.json'];a={}
for n in names:
 p=B/n
 for f in sorted(p.rglob('*')) if p.is_dir() else [p]:
  if f.is_file():a[str(f.relative_to(B))]=h(f)
out('frozen-after.json',a);before=json.loads((R/'frozen-before.json').read_text());assert a==before
bindings={}
for p in (B/'sigma-formal-r2/Sigma').glob('*.lean'):
 assert p.read_bytes()==(R/'proof/Sigma'/p.name).read_bytes();bindings['Sigma/'+p.name]=h(p)
p=B/'sigma-formal-r2/NegativeControls.lean';assert p.read_bytes()==(R/'proof/NegativeControls.lean').read_bytes();bindings[p.name]=h(p)
assert len(bindings)==12
out('receipts/frozen-preservation.json',dict(status='PASS',regular_files=len(a),before_sha256=h(R/'frozen-before.json'),after_sha256=h(R/'frozen-after.json'),identical_module_bindings=bindings,orientation_reads_before_baseline=True))
q=[]
notes=['Title, definitions, quantifiers and draft label readable; generous title-page white space.','Variance/deficit equations, attribution and n=10 comparison clear.','Walk proof readable; missing set-difference glyph replaced by the word minus.','Triple injection and sanity values readable, no clipping.','Bracketing, small-order bounds and classification readable.','Correspondence table fits; long names and pins readable.','Literature limits and references readable; footer clear.']
for i in range(1,8):q.append(dict(page=i,png='qa/page-'+str(i)+'.png',sha256=h(R/('qa/page-'+str(i)+'.png')),visually_inspected=True,status='PASS',notes=notes[i-1]))
out('qa/receipt.json',dict(status='PASS',pages=7,pdf_sha256=h(R/'paper.pdf'),method='Every final page PNG opened and visually inspected by the authoring agent; second rendering after glyph correction.',pages_review=q))
receipts=[json.loads(p.read_text()) for p in (R/'final-extraction/replay-receipts').glob('*.json') if p.name not in ['declarations.json','result.json']]
assert all(p['kill_reason'] is None and p['exit']==p['expected'] for p in receipts)
assert all(p['systemd_MemoryMax_6G'] for p in receipts)
# Confirm no subprocess from the replay remains. This script's own scope is excluded.
live=[]
for p in Path('/proc').glob('[0-9]*/cmdline'):
 try:
  cmd=p.read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if str(R/'final-extraction') in cmd and ('/bin/lean ' in cmd or '/bin/leanchecker ' in cmd or 'replay.py' in cmd):live.append(dict(pid=int(p.parent.name),cmd=cmd))
 except OSError:pass
assert not live,live
out('results.json',dict(status='DRAFT',mathdb_id=365710,accepted_credit=0,campaign_count='6/20 beyond 39 unchanged',acceptance_authority='root alone',replay=res,final_source_archive_sha256=h(R/'source-only-proof.zip'),frozen_inputs='UNCHANGED',frozen_regular_files=len(a),byte_identical_modules=12,visual_QA='PASS: all 7 final pages inspected',axiom_whitelist=['propext','Classical.choice','Quot.sound'],systemd_scope_all_replay_commands=True,peak_private_RSS_bytes=max(p['peak_private_RSS_bytes'] for p in receipts),peak_total_VmRSS_bytes=max(p['peak_total_VmRSS_bytes'] for p in receipts),novelty='QUALIFIED_PASS by supplied root adjudication; reviewer HOLDs and unread bodies disclosed',running_replay_jobs=live,limitations=['Bell 1992, Réti 2019, Dimitrov–Stevanović 2023 bodies unread','Initial orientation reads preceded baseline; subsequent work hash-bound','No new external novelty search or acceptance in this lane','Pinned upstream cached objects trusted, not rebuilt']))
(R/'SUMMARY.md').write_text('''# MathDB 365710 — DRAFT dossier

Seven-page manuscript and reproducible certificate prepared. Zero accepted credit; root alone accepts. Campaign count remains 6/20 beyond 39. No publication, upload, git, child agents, browser, external messages or shared-lane writes were used.

The theorem bounds the exact unordered all-pair squared-degree invariant over every connected triangle-free graph, proves attainment by maximizing positive complete-bipartite parts, and proves that only such complete bipartite graphs attain. The singleton is separate. The ordinary proof credits Zhou 2004 for the deficit identity; its extra structural gap D >= n-2 overcomes integer rounding. The manuscript includes the n=10 classical-bound obstruction and exact small-order comparisons.

Final fresh extraction of source-only-proof.zip: PASS. Thirteen strict sequential builds and thirteen leanchecker runs cover 11 Sigma modules, NegativeControls and ReviewerSanity. The full audit records 130 local/generated declarations, with actual bodies, safe/nonpartial status, full types and only propext, Classical.choice, Quot.sound transitively. Three false finite mutations are rejected as expected; these tests claim only those rejections. Details: final-extraction/replay-receipts/result.json, declarations.json and individual logs/receipts. Earlier extraction receipts are retained locally as a preliminary run; final receipts bind the delivered archive. No upstream caches are bundled or mutated.

All seven final pages were rendered and visually inspected. qa/receipt.json binds each inspected PNG and the PDF. The fonts are included for reproducible rendering; write_paper.py and paper-content.json are the manuscript source. All 12 frozen mathematical/control modules (11 Sigma plus NegativeControls) are byte-identical. Complete input-tree inventories are equal before and after. Initial orientation reads preceded the baseline; this is not represented as a before-first-read freeze. The initial generic marker path was absent and the document-format-only marker rejected pdf; the installed PDF skill's own marker then succeeded before manuscript authoring. ReportLab and bundled fonts were located after two local setup failures; final rendering succeeded.

The supplied root novelty ruling is QUALIFIED_PASS, with reviewer HOLDs preserved. Bell 1992, Réti 2019 and Dimitrov–Stevanović 2023 bodies remain unread, explicitly disclosed. No worldwide priority or exhaustive literature clearance is claimed. No fresh external search was undertaken.

REPRODUCE.md documents environment overrides, trusted dependency pins, fresh-only refusal behavior and caps. Every final replay subprocess used at most two affinity CPUs, CPU 120 s, wall 140 s, AS 64 GiB, MALLOC_ARENA_MAX=2, sampled 6 GiB private RSS guard, total VmRSS reporting and an available systemd MemoryMax=6G scope. The dossier includes receipts rather than upstream caches or compiled objects. No replay jobs remain running.

Deliverables: paper.pdf; write_paper.py and paper-content.json; PROOF.md; source-only-proof.zip; full-dossier.zip; source-manifest.json; dossier-manifest.json; archive-hashes.json; results.json. The full archive excludes itself, external caches, compiled payloads, temporary Python cache files and redundant extraction trees; it includes final replay receipts under final-extraction/replay-receipts.
''')
(R/'MANIFEST-NOTES.md').write_text('Source manifest maps every payload path to SHA-256; it excludes itself. Dossier manifest binds final deliverables and receipts, excluding itself and archive-hashes.json. Full ZIP includes that manifest. archive-hashes.json is outside both ZIPs and binds both archives, avoiding circular hashes. Frozen manifests bind input bytes, not acceptance. Local extraction objects exist only as replay products; no olean/ilean payload is distributed.\n')
# Full dossier contains final evidence, no redundant extracted sources or compiled files.
files=[]
for p in sorted(R.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(R)
 if rel.parts[0] in ['fresh-extraction','__pycache__','finalization-receipts']:continue
 if rel.parts[0]=='final-extraction' and (len(rel.parts)<2 or rel.parts[1]!='replay-receipts'):continue
 if p.suffix in ['.olean','.ilean','.pyc','.zip'] or p.name in ['archive-hashes.json','dossier-manifest.json','launch.json']:continue
 files.append(p)
out('dossier-manifest.json',{str(p.relative_to(R)):h(p) for p in files})
with zipfile.ZipFile(R/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[R/'dossier-manifest.json']:z.write(p,str(p.relative_to(R)))
out('archive-hashes.json',{n:h(R/n) for n in ['source-only-proof.zip','full-dossier.zip']})
print(json.dumps(json.loads((R/'results.json').read_text()),indent=2))
