"""Finalize receipts and deterministic archives, inside the assigned lane only."""
import os,resource,pathlib,json,hashlib,zipfile,re,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(1900000000,1900000000))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
D=pathlib.Path(__file__).resolve().parent;B=D.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def save(name,obj):(D/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
before=json.loads((D/'inputs-before.json').read_text())
after={p:sha(B/p) for p in before}
save('inputs-after.json',after)
assert before==after,'Frozen input changed'
anc=json.loads((D/'ancillary-before.json').read_text());anca={p:sha(pathlib.Path(p)) for p in anc}
save('ancillary-after.json',anca)
assert anc==anca,'Ancillary input changed'
pdfsha=sha(D/'manuscript.pdf')
images=sorted((D/'qa').glob('page-*.png'));assert len(images)==6
text=(D/'qa/manuscript-extracted.txt').read_text()
assert len([p for p in text.split('\f') if p.strip()])==6
assert all(s in text for s in ['Conjecture 1','105','75','9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200','embargo','19.2.5'])
save('qa/visual-inspection.json',{'status':'PASS','method':'Poppler pdftoppm at 110 dpi; each of six final page images opened and visually inspected by implementation agent','manuscript_sha256':pdfsha,'pages':[{'page':i+1,'image':str(p.relative_to(D)),'sha256':sha(p),'observations':v} for i,(p,v) in enumerate(zip(images,['Title, source definitions, exact conjecture and draft/AI disclosure legible; no clipping.','Literal word, all occurrence positions and finite proof legible; no overlap.','All edge subwords and complete pair matrix legible, with bottom paragraph clear of footer.','Formal correspondence, archive hash, replay attribution and trust limits fit cleanly.','Related work, embargo limitation, generic SMT predecessor and modest scope fully visible.','Reproduction details, bibliography, DOI and source-retention evidence fit cleanly.']))],'layout_receipt':'manuscript.layout.json','text_extraction':'qa/manuscript-extracted.txt','defects_found':0})
fonts=[pathlib.Path('/usr/share/fonts/liberation-serif-fonts/LiberationSerif-'+s+'.ttf') for s in ['Regular','Bold']]
save('build-receipt.json',{'status':'PASS','pdf_sha256':pdfsha,'pages':len(images),'source_files':['build_paper.py','pdf_engine.py','manuscript.md'],'fonts':{str(p):sha(p) for p in fonts},'renderer':'system Poppler pdftoppm','python_isolated':True,'peak_build_rss_kib':18456,'fresh_verifier_peak_rss_kib':json.loads((D/'verification.json').read_text())['sampled_peak_rss_kib'],'limits':{'cpus':2,'cpu_seconds':120,'wall_seconds':140,'address_space_bytes':1900000000,'malloc_arena_max':2},'diagnostics':['Initial ReportLab import failed: package unavailable; no installation attempted.','Initial custom build identified an unsupported mapsto glyph; source uses readable words maps to.','Final self-contained PDF writer asserts every glyph is available and every page fits.'],'administrative_note':'Initial brief-only cat was not explicitly resource-wrapped; short read-only command. Later invocations explicitly bounded. No compute ran unbounded.','new_lean_or_solver_runs':0})
save('input-integrity.json',{'status':'PASS','frozen_files':len(before),'before_equals_after':True,'copied_files':len(json.loads((D/'copy-receipt.json').read_text())),'ancillary_files':len(anc),'ancillary_unchanged':True,'packet_byte_identical':True})
save('results.json',{'schema_version':1,'mathdb_id':369421,'status':'DRAFT_PACKAGE_READY_FOR_ROOT_REVIEW','accepted':False,'accepted_credit':0,'scope':'Refutation of Conjecture 1 only, using the explicit 3-representation of C_3 square C_5','endpoint':'Toroidal.mathdb_369421 : ¬ Toroidal.Conjecture1','fresh_ordinary_verification':'PASS','safe_extraction':'PASS','frozen_input_integrity':'PASS','pdf_pages':6,'all_pdf_pages_visually_inspected':True,'formal_replay':'Prior independent review and root PASS receipts preserved; no new formal execution here','registry':'Root CLEAN receipt preserved; bounded path/topic screen, no new network request','qualifications':['Accepted JALC manuscript is embargoed and unread; exact accepted-body retention unverified.','Generic positional SMT encoding and representation-number tool already exist; no new-method claim.','Bounded prior-art screen; no priority claim; significance modest.'],'ai_assistance':True,'human_authors_asserted':False,'campaign_context':'38/40 beyond 39 per task; no count changed','root_alone_accepts':True,'children_spawned':0,'background_jobs_at_handback':0,'outputs':{'pdf':'manuscript.pdf','source':['manuscript.md','build_paper.py','pdf_engine.py'],'dossier':'toroidal-369421-full-dossier.zip','paper_bundle':'toroidal-369421-paper.zip','manifest':'MANIFEST.sha256','archive_hashes':'archives.sha256'}})
(D/'SUMMARY.md').write_text('''# MathDB 369421 manuscript package

**DRAFT; AI-assisted; zero accepted credit. Root alone accepts.**

The six-page manuscript gives the explicit word, source definitions and verbatim
Conjecture 1, a direct finite proof, occurrence positions, all edge subwords and
the full pair matrix, formal correspondence, trust limits, related work and
qualified significance. The fresh independent checker verifies all pairs by
both filtered-letter comparison and strict positional interlacing and matches
the Lean coordinate literal. All mathematical counts and table entries are
regenerated; numeric source metadata has a separate provenance check.

The original Lean packet is reused byte-identically with SHA-256
`9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200`.
Safe extraction was actually tested. No Lean, lake, leanchecker or solver was run.
Prior independent and root replay PASS receipts are preserved as prior evidence.
All frozen inputs have matching before/after hashes. Every final manuscript PDF
page was rendered and visually inspected; images and a hash-bound QA receipt are
included. The first ReportLab attempt failed because the package is absent;
the delivered PDF uses a self-contained writer and embedded local fonts.

The significance is modest: a small certificate refutes an explicit universal
conjecture at its first new case. The accepted journal manuscript is embargoed
and unread; author-side and institutional linkage does not prove exact retention
in that body. Generic SMT encoding and a representation-number tool already
exist. There is no new-method or priority claim, no neighbouring-case credit,
and no claim that the exact representation number must equal three.

Deliverables: `manuscript.pdf`, readable `manuscript.md`, authoritative source
`build_paper.py` and `pdf_engine.py`, `PROOF.md`, `REPRODUCE.md`, exact MathDB raw
line and hash, source copies with receipts, byte-identical `lean-packet.tar.gz`,
full evidence/check/QA receipts, `results.json`, manifests, the paper ZIP and full
dossier ZIP. `archives.sha256` binds the ZIPs externally to avoid self-hash cycles.

No network, git, uploads, publication, browser tabs, external messages, shared
ledger edits, cross-lane writes, child agents or persistent jobs were used.
The campaign context remains 38/40 beyond 39 as supplied; no acceptance is made.
Resource and initial read-only wrapper qualifications are documented in
`build-receipt.json` and `REPRODUCE.md`. No jobs remain at handback.
''')
# Manifest excludes only cyclic archive/manifest artifacts and transient caches.
excluded={'MANIFEST.sha256','archives.sha256','archive-receipt.json','final-check-receipt.json','toroidal-369421-full-dossier.zip','toroidal-369421-paper.zip'}
files=sorted(p for p in D.rglob('*') if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts)
(D/'MANIFEST.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(D))+'\n' for p in files))
files.append(D/'MANIFEST.sha256')
def archive(name,paths):
 with zipfile.ZipFile(D/name,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
  for p in paths:
   info=zipfile.ZipInfo(str(p.relative_to(D)),date_time=(2026,11,4,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
   z.writestr(info,p.read_bytes())
 with zipfile.ZipFile(D/name) as z:
  assert z.testzip() is None
  for p in paths:assert hashlib.sha256(z.read(str(p.relative_to(D)))).hexdigest()==sha(p)
 return {'sha256':sha(D/name),'members':len(paths),'bytes':(D/name).stat().st_size,'crc_test':'PASS','every_member_byte_comparison':'PASS'}
names=['toroidal-369421-full-dossier.zip','toroidal-369421-paper.zip']
receipts={names[0]:archive(names[0],files)}
paper=[D/p for p in ['manuscript.pdf','manuscript.md','build_paper.py','pdf_engine.py','PROOF.md','REPRODUCE.md','verification.json','numerical-receipt.json','build-receipt.json']]
receipts[names[1]]=archive(names[1],paper)
save('archive-receipt.json',{'status':'PASS','archives':receipts,'self_hash_policy':'archives.sha256 and this receipt are external to ZIPs; full archive contains MANIFEST.sha256'})
(D/'archives.sha256').write_text(''.join(receipts[n]['sha256']+'  '+n+'\n' for n in names))
print(json.dumps({'frozen_files':len(before),'packaged_files':len(files),'archives':receipts,'finalizer_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},indent=2))
