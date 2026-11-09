from pathlib import Path
import hashlib,json,zipfile,time
D=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,v): (D/n).write_text(json.dumps(v,indent=2)+'\n')
for name in ['inputs','dependency-inputs']:
 before=json.loads((D/(name+'-before.json')).read_text())
 after={p:sha(Path(p)) for p in before}
 write(name+'-after.json',after)
 assert before==after, [p for p in before if before[p]!=after[p]]
write('input-integrity.json',{'frozen_inputs_unchanged':True,'files':len(json.loads((D/'inputs-before.json').read_text())), 'rendering_inputs_unchanged':True,'all_writes_lane_local':True})
b=D.parent;raw=b/'expanded-corpus-r126/raw/338258.jsonl'
assert raw.read_bytes()==(D/'mathdb-338258.raw.jsonl').read_bytes()
write('RAW-RECORD.json',{'mathdb_id':338258,'original':str(raw),'copy':'mathdb-338258.raw.jsonl','sha256':sha(raw),'bytes':raw.stat().st_size,'byte_identical':True,'lines':len(raw.read_bytes().splitlines())})
packet=D/'338258-infinite-family-source.zip'
assert sha(packet)=='27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063'
for p in (D/'proof-packet-safe').glob('*.lean'):
 assert p.read_bytes()==(b/'riordan-formal-r2/formal'/p.name).read_bytes()
checks=['Title, draft and AI disclosure; definitions and conjecture legible.', 'Source spectral statements, block equations and finite/infinite distinction legible.', 'All 15 matrix rows and coefficient recurrence visible; no clipped columns.', 'Both blocks, full vector and cancellation equations visible; nullity argument legible.', 'Infinite-series definition, coefficient prefix, caveat and search scope legible.', 'Correspondence table fits page; both endpoint names wrap legibly.', 'Audit counts, negative controls, trust limits and root replay account legible.', 'Literature and access limits plus all bibliography entries fit page.']
write('qa/receipt.json',{'pdf':'paper.pdf','pdf_sha256':sha(D/'paper.pdf'),'pages':8,'raster_dpi':115,'inspection':'Every final page opened and visually inspected with view_image; body, mathematics, table, margins and page numbering checked. Header/footer text presence also checked with pdftotext.','pages_reviewed':[{'page':i,'image':f'qa/page-{i}.png','sha256':sha(D/f'qa/page-{i}.png'),'finding':c,'body_clipping_or_overlap':False} for i,c in enumerate(checks,1)],'acceptance':False})
source_index={}
for n in ['inputs-before.json','dependency-inputs-before.json']:
 for p,h in json.loads((D/n).read_text()).items():source_index.setdefault(h,[]).append(p)
copies={str(p.relative_to(D)):{'sha256':sha(p),'frozen_originals':source_index[sha(p)]} for p in D.rglob('*') if p.is_file() and sha(p) in source_index}
write('SOURCE-COPIES.json',copies)
r=json.loads((D/'evidence/replay-result.json').read_text());assert r['status']=='PASS'
write('results.json',{'mathdb_id':338258,'lane':'riordan-manuscript-r1','status':'DRAFT complete; root manuscript adjudication required','accepted':False,'credit':0,'root_decides':True,'paper':{'source':'paper.md','pdf':'paper.pdf','pages':8,'all_pages_rendered_and_visually_inspected':True},'proof_packet':{'file':packet.name,'sha256':sha(packet),'byte_identical_reuse':True,'safe_extraction':True,'modules':22},'endpoints':['Riordan.source_conjecture_false','Riordan.source_conjecture_false_infinite_family'],'manuscript_math':{'Ax_zero':True,'canonical_odd_copy':True,'even_independent':True,'minor_deleting_vertex_1':-1,'nullity':1,'minimality_scope':'reviewer computational evidence only, infinite recurrence family, n=2..15'},'review_audit':{'finite_proof_modules':18,'local_declarations':398},'formal_r2_audit':{'modules':22,'proof_modules':20,'local_declarations':450,'dependency_closure':10694},'root_replay':{'available':True,'reported_status':'PASS','report':'evidence/replay-result.json','builds':22,'checker_passes':22,'negative_controls_rejected':3,'sha256':sha(D/'evidence/replay-result.json')},'registry_refresh':{'available':True,'scope':'root bounded complete-tree path screen with targeted read','report':'evidence/registry-refresh.json'},'Lean_lake_leanchecker_executed_by_this_lane':False,'frozen_inputs_unchanged':True,'resources':'at most 2 CPUs (one inherited here); CPU 120 s; wall 140 s; 6 GiB address-space bound and sampled RSS for logged jobs; MALLOC_ARENA_MAX=2; one heavy process at a time','background_jobs_at_handback':0,'priority_claim':False,'literature_limits':['bounded reviewer screen','publisher final body not accessed','Pascal spectral paper full body not obtained','no worldwide novelty certification']})
(D/'SUMMARY.md').write_text('''# Draft manuscript handback - MathDB 338258

DRAFT complete; **zero accepted credit**. Root alone decides acceptance.

- Eight-page paper: paper.pdf, editable source paper.md, renderer scripts/render.py. Every final page rendered and visually inspected; qa/receipt.json binds the images to the PDF.
- Readable full matrix and block/kernel certificate, canonical io conditions, nullity 1 via principal minor -1, infinite extension and coefficient locality. Finite n = 7 twin example is only a definitional remark. Minimality is reviewer computational evidence within the infinite-recurrence family only.
- Both formal endpoints are described accurately. The exact source-only ZIP is reused byte-identically, SHA-256 27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063. Safe extraction passed without invoking a prover.
- Root replay arrived before manuscript freeze: evidence/replay-result.json records PASS, 22 builds, 22 checker passes and three rejected negative controls. Root registry refresh is included. These are attributed reports, not this lane's prover runs or acceptance.
- PROOF.md, correspondence, exact raw MathDB line with hash, primary source copies/receipts, review/search/certificate evidence, reproduction instructions and manifests are included in riordan-full-dossier.zip.
- Frozen inputs and rendering dependencies hash-identical before/after. No Lean, lake, leanchecker, git, child agents, browser tabs, uploads, messages or shared edits. No running jobs at handback.

Prior art remains bounded; no priority claim. Publisher final text and the full Pascal spectral paper remain access limitations. See REPRODUCE.md for package closure and trust limits. DELIVERY-SHA256.json gives the final external delivery hashes.
''')
exclude={'DOSSIER-MANIFEST.json','riordan-full-dossier.zip','DELIVERY-SHA256.json','package-validation.json','logs/package-sealed.log','logs/package-sealed.receipt.json'}
files=sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in exclude)
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p)}for p in files}
write('DOSSIER-MANIFEST.json',manifest)
with zipfile.ZipFile(D/'riordan-full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[D/'DOSSIER-MANIFEST.json']:z.write(p,str(p.relative_to(D)))
with zipfile.ZipFile(D/'riordan-full-dossier.zip') as z:
 assert set(z.namelist())==set(manifest)|{'DOSSIER-MANIFEST.json'}
 for p,v in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==v['sha256']
write('package-validation.json',{'passed':True,'members':len(files)+1,'all_member_hashes_match':True,'source_packet_sha256':sha(packet),'no_running_background_jobs':True})
write('DELIVERY-SHA256.json',{n:sha(D/n)for n in ['paper.pdf','paper.md','PROOF.md','results.json','SUMMARY.md','338258-infinite-family-source.zip','riordan-full-dossier.zip','DOSSIER-MANIFEST.json','package-validation.json','qa/receipt.json']})
print('Dossier sealed:',len(files)+1,'members;', (D/'riordan-full-dossier.zip').stat().st_size,'bytes')
