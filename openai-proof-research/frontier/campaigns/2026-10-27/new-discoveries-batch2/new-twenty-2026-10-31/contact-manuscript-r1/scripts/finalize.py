from pathlib import Path
import json,hashlib,shutil,zipfile,subprocess,datetime,os
p=Path(__file__).resolve().parents[1];b=p.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def write(path,v):path.write_text(json.dumps(v,indent=2)+'\n')
logs=p/'work/extracted-01/replay-logs'
assert json.loads((logs/'complete.json').read_text())['status']=='PASS'
shutil.copytree(logs,p/'receipts/fresh-replay',dirs_exist_ok=True)
shutil.copytree(b/'contact-formal-r5/work/extracted-01/replay-logs',p/'evidence/r5-fresh-replay',dirs_exist_ok=True)
# Bind every declared frozen file again and compare byte-for-byte.
h=json.loads((p/'receipts/frozen-before.json').read_text())
a={n:sha(Path(n)) for n in h};write(p/'receipts/frozen-after.json',a)
assert a==h
mods={q.name:sha(q) for q in (p/'formal').glob('*.lean')}
assert len(mods)==28
assert all(sha(b/'contact-formal-r5/formal'/n)==v for n,v in mods.items())
write(p/'MODULE-HASHES.json',mods)
write(p/'receipts/frozen-bindings.json',{'status':'PASS','frozen_file_count':len(h),'all_unchanged':True,'lean_modules_byte_identical':28,'frozen_packet_sha256':sha(b/'contact-formal-r5/contact-r5-source.zip')})
# Actual pin evidence; no git command or mutation.
cache=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
head=(cache/'mathlib/.git/HEAD').read_text().strip();assert head=='d13f23b723b8a846827a245b89c10fc7d3f11612'
manifest=cache.parent.parent/'lake-manifest.json'
shutil.copy2(manifest,p/'evidence/lake-manifest.json')
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
version=subprocess.check_output([str(lean),'--version'],text=True)
write(p/'receipts/pin-verification.json',{'lean_version_output':version,'lean_executable_sha256':sha(lean),'leanchecker_sha256':sha(lean.with_name('leanchecker')),'mathlib_HEAD':head,'lake_manifest_sha256':sha(manifest),'dependency_source_rebuild':False})
info=subprocess.check_output(['pdfinfo',str(p/'paper/contact-draft.pdf')],text=True)
(p/'receipts/pdfinfo.txt').write_text(info);assert 'Pages:           8' in info
images=sorted((p/'qa').glob('page-*.png'));assert len(images)==8
write(p/'receipts/pdf-visual-qa.json',{'status':'PASS','pdf_sha256':sha(p/'paper/contact-draft.pdf'),'pages':8,'method':'pdftoppm at 110 dpi; each final page viewed individually through view_image','reviewer':'implementation agent (AI)','checks':['all eight final pages inspected','headings rendered without Markdown markers','formulas and matrix legible','no clipped or overlapping text','consistent page numbers and footer','bibliography complete and readable'],'images':{q.name:sha(q) for q in images},'iterations':'Fixed page-break parsing and heading parsing; first build also required local font-path correction. Retained build logs record those iterations.'})
rs=[json.loads(q.read_text()) for q in logs.glob('*.receipt.json')]
assert len(rs)==69 and all(v['killed'] is None for v in rs)
for q in logs.glob('*.receipt.json'):
 r=json.loads(q.read_text());assert r['returncode']==(1 if q.name.startswith('negative-') else 0)
inventory=json.loads((logs/'audit-inventory.json').read_text());assert inventory['declaration_count']==314
result={'mathdb_id':365301,'status':'draft_dossier_complete_awaiting_root_review','accepted_credit':0,'campaign_count_unchanged':'22/40 beyond previous 39','endpoint':'ContactPilot.refutation : ¬ ContactPilot.SourceConjecture','ordinary_result':{'nearest_w_distance':1,'contact_order':6,'branch_orders':[6,2]},'verification':{'fresh_extracted_replay':'PASS','strict_builds':28,'separate_leanchecker_processes':28,'declarations_audited':314,'failing_Lean_negative_controls':13,'additional_audit_negative_controls':4,'all_28_modules_byte_identical_to_r5':True,'calls':69,'peak_sampled_RSS_bytes':max(v['peak_rss_bytes'] for v in rs),'max_call_wall_seconds':max(v['wall'] for v in rs),'watchdog_kills':0,'frozen_files_unchanged':len(h),'paper_pages_rendered_and_visually_inspected':8,'prose_symbolic_checks':'PASS'},'allowed_axioms':['propext','Classical.choice','Quot.sound'],'limits':['Root final source-fidelity review and replay required','No priority claim; inherited bounded prior-art ruling only','Source journal body unread; ScienceDirect excluded','Cached dependencies not rebuilt from source'],'deliverables':['paper/contact-draft.pdf','paper/contact-draft.md','paper/build_paper.py','PROOF.md','REPRODUCE.md','contact-source-only.zip','contact-full-dossier.zip','SOURCE-MANIFEST.json','DOSSIER-MANIFEST.json','MODULE-HASHES.json'],'no_background_jobs':True}
write(p/'results.json',result)
(p/'SUMMARY.md').write_text(f'''# MathDB 365301: draft manuscript and reproducible dossier

Completed the eight-page AI-assisted DRAFT paper and ordinary proof. The five-vertex graph has nearest-w distance 1 and contact order 6, with analytic branch orders 6 and 2. The literal endpoint is `ContactPilot.refutation : ¬ ContactPilot.SourceConjecture`.

Fresh safe extraction of `contact-source-only.zip` passed all 28 strict serial Lean builds, 28 separate leanchecker calls, a full 314-declaration audit and 13 failing Lean negative controls. Four additional audit controls verify rejection of unsafe, partial, compiler-generated `_unsafe_rec` and extra axioms. All 28 Lean modules are byte-identical to contact-formal-r5. Maximum sampled RSS was {result['verification']['peak_sampled_RSS_bytes']:,} bytes; maximum individual replay call wall time was {result['verification']['max_call_wall_seconds']:.2f} seconds. No watchdog killed a call. Every final PDF page was rendered and visually inspected.

Deliverables: `paper/contact-draft.pdf`, its Markdown and ReportLab source, `PROOF.md`, `STATEMENT-CORRESPONDENCE.md`, `REPRODUCE.md`, pins, exact MathDB raw line with hash, source bodies and access receipts, both ZIPs, manifests, and replay evidence in `receipts/fresh-replay`. `receipts/frozen-bindings.json` confirms {len(h)} frozen files unchanged before/after. The source ZIP is the minimal Lean replay packet; the full ZIP adds all manuscript, source and dossier evidence, without compiled objects or the duplicate extraction tree.

No git, shared ledger edits, external messages, browser use, publication or uploads. No background jobs remain. All writes stayed inside this lane. Resource-capped processes ran one at a time. Initial PDF build/layout errors were corrected before final rendering; logs are retained.

Zero accepted credit. Counts stay 22/40 beyond the previous 39. Root alone accepts after final replay and paper/source-fidelity review. The source journal body remains unread; inherited prior-art clearance is qualified and bounded. No priority claim is made.
''')
write(p/'receipts/replay-observation.json',{'status':'PASS','final_line_observed':'PASS: strict build, leanchecker, declaration audit and thirteen negative controls','session_exit_code':0,'fresh_extraction':'work/extracted-01','archive_sha256':sha(p/'contact-source-only.zip'),'complete_receipt':'fresh-replay/complete.json','no_background_jobs':True})
# Full archive: no extracted build, bytecode, archive cycles or transient cap log.
exclude={'contact-full-dossier.zip','DOSSIER-MANIFEST.json','archive-hashes.json'}
def included(q):
 rel=q.relative_to(p)
 return q.is_file() and not q.is_symlink() and rel.parts[0]!='work' and q.name not in exclude and not q.name.endswith(('.olean','.ilean','.ir','.pyc')) and '__pycache__' not in rel.parts and q.name not in ['finalize.log','finalize.log.receipt.json','archive-verification.json']
files=sorted(q for q in p.rglob('*') if included(q))
m={str(q.relative_to(p)):sha(q) for q in files};write(p/'DOSSIER-MANIFEST.json',{'algorithm':'SHA-256','excludes':'This manifest, full ZIP, archive hash receipt, transient finalization log and post-archive verification; extraction/build tree omitted.','files':m})
with zipfile.ZipFile(p/'contact-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for q in files+[p/'DOSSIER-MANIFEST.json']:z.write(q,q.relative_to(p))
with zipfile.ZipFile(p/'contact-full-dossier.zip') as z:
 assert z.testzip() is None
 for n,v in m.items():assert hashlib.sha256(z.read(n)).hexdigest()==v
write(p/'archive-hashes.json',{n:sha(p/n) for n in ['contact-source-only.zip','contact-full-dossier.zip']})
write(p/'receipts/archive-verification.json',{'status':'PASS','full_zip_CRC':True,'all_dossier_manifest_members_verified':len(m),'source_zip_fresh_replay':'PASS','compiled_artifacts_distributed':False})
print(json.dumps({'status':'PASS','dossier_files':len(m),'replay':result['verification'],'archives':json.loads((p/'archive-hashes.json').read_text())},indent=2))
