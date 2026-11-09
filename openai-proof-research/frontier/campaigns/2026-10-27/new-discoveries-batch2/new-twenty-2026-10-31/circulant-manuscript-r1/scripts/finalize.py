from pathlib import Path
import hashlib,json,zipfile,datetime
W=Path(__file__).resolve().parents[1]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,obj):(W/p).write_text(json.dumps(obj,indent=2)+'\n')
replay=json.loads((W/'fresh-replay/receipts/replay.json').read_text());assert replay['status']=='PASS'
before=json.loads((W/'input-hashes-before.json').read_text());after={p:h(Path(p)) for p in before};assert before==after
write('input-hashes-after.json',after)
write('receipts/frozen-integrity.json',{'status':'PASS','files':len(before),'unchanged':before==after,'before_sha256':h(W/'input-hashes-before.json'),'after_sha256':h(W/'input-hashes-after.json')})
receipts=[json.loads(p.read_text()) for p in (W/'fresh-replay/receipts').glob('*.json') if p.name!='replay.json']
peak=max(r.get('peak_RSS_KiB',0) for r in receipts)
write('results.json',{'350979':{'status':'DRAFT manuscript and reproducible dossier complete; root acceptance pending','accepted_credit':0,'theorem':'Every order-15 circulant with diameter 2 has mp-number at least 3; not SourceClaim','classification':{'triangle':109,'distance_obstruction':17,'residual_masks':[41,70]},'residual_exact_mp':6,'coverage':{'lower':11,'upper':40,'exists_except':[15],'above_40':'OPEN / no claim'},'fresh_safe_extracted_replay':replay,'sampled_peak_RSS_KiB':peak,'frozen_inputs_unchanged':True,'source_modules_byte_identical':True,'draft_pdf_pages':5,'pdf_qa':'PASS, all pages visually inspected','prior_art_limits':['journal body unread, HTTP 403','bounded selective literature review only','known residual graph and product-formula mp calculation; no separate novelty or priority claim'],'source_zip':'circulant-source-only.zip','full_zip':'circulant-full-dossier.zip','no_background_jobs':'All launched jobs completed before finalization','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}})
(W/'SUMMARY.md').write_text('''# MathDB 350979: draft manuscript and dossier

Complete within circulant-manuscript-r1. Zero accepted credit; root alone accepts.

The five-page draft proves that every order-15 circulant with diameter 2 has mp-number at least 3, refuting the exact universal existential quantifier in Conjecture 4.5. The proof includes the triangle and open-twin lemmas, the 128-mask classification and a table of all 19 triangle-free masks. The residual graphs are familiar C5[3K1] blow-ups, with exact mp-number 6; the known product formula gets no separate credit. Verified positive witnesses cover every order 11 through 40 except 15. The corrected question excluding 15 remains open beyond that range.

- paper/circulant-draft.pdf: five-page AI-assisted DRAFT, with explicit trust and access limits.
- paper/manuscript.json and paper/build_paper.py: editable text and PDF builder.
- PROOF.md and STATEMENT-CORRESPONDENCE.md: ordinary proof and correspondence.
- circulant-source-only.zip: clean portable proof sources, AuditFull, controls, drivers and certificates.
- circulant-full-dossier.zip: source materials, receipts, paper, rendered QA and complete dossier (no local oleans).
- REPRODUCE.md, pins.json and SOURCE-MANIFEST.json: replay instructions and pins.
- fresh-replay/receipts/replay.json: PASS after safe fresh extraction of the source-only ZIP.
- fresh-replay/logs/build-AuditFull.log: full types, bodies and axiom data for all 52 local declarations, including generated ones.
- receipts/frozen-integrity.json: all 372 frozen original input files unchanged.
- INPUT-COPY-MANIFEST.json, MODULE-HASHES.json, DOSSIER-MANIFEST.json and archive-hashes.json: SHA-256 bindings.

Validation: fresh sequential strict builds and one-module-per-process leanchecker runs passed for all seven modules; both false controls failed for the intended false-decision reason. Independent certificates verified all 128 masks and all triple-path witnesses at the 29 positive orders. Only propext, Classical.choice and Quot.sound occur transitively. All five PDF pages were rendered and visually inspected. No child agents, git, shared-ledger edits, browser, publication, uploads or external messages were used. No launched job remains running.

The journal body remains unread (403); worldwide priority and a complete citing-literature census are not established. Cached mathlib oleans are trusted and not rebuilt. The exact mp=6 and coverage computations supplement rather than extend the literal Lean source_refutation endpoint. Root must still perform its final replay, paper review and acceptance decision.
''')
# No archives, generated local compiler environments, or extraction duplication in the full dossier.
files=[]
for p in sorted(W.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(W)
 if rel.parts[0] in ['fresh-replay','tmp']:
  if rel.parts[0]=='tmp':continue
  if len(rel.parts)<2 or rel.parts[1] not in ['logs','receipts']:continue
 if p.suffix in ['.olean','.ilean','.pyc'] or '.olean.' in p.name or '__pycache__' in rel.parts:continue
 if p.name in ['circulant-full-dossier.zip','DOSSIER-MANIFEST.json','archive-hashes.json']:continue
 files.append(p)
write('DOSSIER-MANIFEST.json',{str(p.relative_to(W)):h(p) for p in files})
files.append(W/'DOSSIER-MANIFEST.json')
with zipfile.ZipFile(W/'circulant-full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,str(p.relative_to(W)))
write('archive-hashes.json',{p:h(W/p) for p in ['circulant-source-only.zip','circulant-full-dossier.zip']})
with zipfile.ZipFile(W/'circulant-full-dossier.zip') as z:
 assert z.testzip() is None
 manifest=json.loads(z.read('DOSSIER-MANIFEST.json'))
 for name,digest in manifest.items():assert hashlib.sha256(z.read(name)).hexdigest()==digest,name
 assert not any('.olean' in name for name in z.namelist())
print('PASS: frozen bindings unchanged; ZIP integrity and full archived manifest verified; peak RSS KiB',peak)
