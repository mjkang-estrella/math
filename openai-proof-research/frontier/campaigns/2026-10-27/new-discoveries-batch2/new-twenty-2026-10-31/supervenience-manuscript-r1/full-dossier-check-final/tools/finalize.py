from pathlib import Path
import hashlib,json,zipfile,shutil,sys,os
D=Path(__file__).resolve().parents[1];os.chdir(D)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
b=D.parent
before=json.loads(Path('frozen-before.json').read_text());after={}
for n in ['expanded-corpus-r84','supervenience-review-r1','supervenience-root-adjudication-r1.json']:
 p=b/n
 for f in sorted(p.rglob('*')) if p.is_dir() else [p]:
  if f.is_file():after[str(f.relative_to(b))]=sha(f)
write('frozen-after.json',after);assert before==after
assert sha('proof/Hierarchy.lean')==sha(b/'expanded-corpus-r84/lean/Hierarchy.lean')
shutil.copyfile(b/'expanded-corpus-r84/hierarchy-packet.zip','reviewer/author-original-hierarchy-packet.zip')
write('receipts/frozen-bindings.json',{'status':'PASS','files':len(before),'before_sha256':sha('frozen-before.json'),'after_sha256':sha('frozen-after.json'),'all_equal':True,'literal_Lean_byte_identical':True})
# Raw source and retrieval receipt binding, including the known unavailable journal response.
for src,receipt in [('sources/1611.04740.pdf','sources/1611.04740.pdf.receipt.json'),('sources/1609.07398.pdf','sources/1609.07398.pdf.receipt.json'),('sources/humberstone.pdf','reviewer/receipt-humberstone.pdf.json')]:
 r=json.loads(Path(receipt).read_text());assert sha(src)==r['sha256'],src
write('receipts/provenance.json',{'raw_MathDB_line_sha256':sha('raw/334599.jsonl'),'literal_module_sha256':sha('proof/Hierarchy.lean'),'copied_sources':{str(p):sha(p) for p in sorted(Path('sources').iterdir()) if p.is_file()},'reads_this_lane':['Fan Definitions 2,6; Section 6 and Conjecture 15; Section 6.1/Proposition 16; Sections 7.3-7.4','Goranko-Kuusisto Definition 3.2 and Proposition 3.3 with proof','Humberstone pp. 15-17 from retained text'],'journal':'unread; challenge retained; no external retrieval by this lane','reviewer_supplements':'Historical reviewer sources, logs and ruling; not acceptance.'})
sys.path.insert(0,str(D/'local-deps'))
from pypdf import PdfReader
pdf=Path('output/pdf/supervenience-draft.pdf')
reader=PdfReader(pdf);assert len(reader.pages)==6
write('qa/receipt.json',{'status':'PASS','pdf_sha256':sha(pdf),'pages':6,'method':'Each final 100 dpi page PNG inspected directly with view_image by the primary agent','checks':['all pages readable','no clipping or overlaps','no missing mathematical glyphs','correspondence table fits','references and footer fit'],'images':{str(p):sha(p) for p in sorted(Path('qa').glob('page-*.png'))},'page_text_characters':[len(p.extract_text()) for p in reader.pages]})
replay=json.loads(Path('fresh-replay-final/replay-receipts/replay.json').read_text());assert replay['status']=='PASS'
models=json.loads(Path('logs/model-check.json').read_text())
assert sum(models['local_pair_exhaustive_counts'].values())==263185
assert models['nested_pointed_cases']==98304
assert len(models['negative_controls'])==5
write('results.json',{'status':'DRAFT','mathdb_id':334599,'accepted_credit':0,'campaign_count':12,'campaign_target':20,'prior_count':39,'acceptance_authority':'root alone','manuscript_pages':6,'literal_endpoint':'Supervenience.literal_conjecture_false','strict_fresh_replay':'PASS','audit_declarations':101,'allowed_axioms':replay['allowed_axioms'],'frozen_inputs_files':len(before),'frozen_inputs_unchanged':True,'byte_identical_module':True,'finite_diagnostics':{'status':'PASS','one_step':263185,'nested_pointed':98304,'negative_control_witnesses':5,'role':'diagnostics only'},'pdf_QA':'PASS all 6 pages inspected','limitations':['Fan journal body unread','bounded literature coverage','no priority claim','trusted upstream cached oleans and toolchain'],'initial_failures':['Initial PDF font path missing; corrected to local Liberation/Noto with glyph fallbacks','Initial replay leanchecker could not locate lean via PATH; portable driver corrected; clean new extraction replay passed'],'writes':'assigned lane only','no_jobs_remaining':True})
Path('SUMMARY.md').write_text("""# MathDB 334599: DRAFT manuscript and reproducible dossier

Six-page manuscript: output/pdf/supervenience-draft.pdf; source: paper.md and build_paper.py.
Ordinary proof: PROOF.md. Literal certificate: proof/Hierarchy.lean (byte-identical to the frozen author module).
Reproduction instructions: REPRODUCE.md. Portable drivers: tools/replay.py and tools/extract.py.

The proof defines the guard D(A; A and B), applies the known four Boolean cells, and proves recursive translation from L2 to L1 on arbitrary ternary frames. It refutes arXiv Conjecture 15 at n = 1, defines Section 7.3 relativized agreement, and identifies the unnecessary single-formula compression premise in Humberstone 2019, pp. 16-17. Known cell techniques are credited; journal text unread and bounded prior-art coverage are explicit. No priority claim.

Fresh safe extraction of source-only-proof.zip into fresh-replay-final passed strict -j1 -DwarningAsError=true compilation of all three modules and leanchecker on each. Module-origin audit checks all 101 original declarations, full types, bodies and safety; only propext, Classical.choice, Quot.sound appear. Receipts: fresh-replay-final/replay-receipts/replay.json and adjacent logs. Deliberately false proof and sorry are rejected; injected local axiom is detected by the audit.

Finite diagnostics were independently rerun: 263185 one-step cases, 98304 nested pointed comparisons, and five negative-control witnesses. These are diagnostics only. Every final PDF page was rendered and visually inspected; qa/receipt.json binds all six images and the PDF.

All 429 frozen input files hash identically before and after; only target-relevant r84 evidence is included. Source-only and full-dossier ZIPs have manifests and external archive hashes. Upstream pinned caches and the Lean distribution remain trusted and unmodified. Each substantive command used the retained limiter; systemd MemoryMax=6G was available. Early font and PATH failures are retained, with successful final replacements. No jobs from this lane remain.

DRAFT. Zero accepted credit. Count stays 12/20 beyond 39. Root alone accepts. No child agents, git, browser, external messages, upload, publication, shared-ledger edits or other-lane writes.
""")
# Full dossier: explicit directories; no private Python installation, transient compiled files,
# or duplicated full extractions. Include failed replay logs for transparency.
files=[]
for n in ['TASK.txt','launch.json','SUMMARY.md','results.json','REPRODUCE.md','PROOF.md','DEPENDENCIES.json','paper.md','build_paper.py','frozen-before.json','frozen-after.json','source-manifest.json','source-only-proof.zip']:
 if Path(n).exists():files.append(Path(n))
for n in ['proof','tools','sources','reviewer','raw','logs','receipts','output','qa','fresh-replay-final/replay-receipts','fresh-replay/replay-receipts']:
 files += [p for p in Path(n).rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in ['.pyc','.olean']]
files=sorted(p for p in set(files) if str(p) not in ['receipts/finalize.log','receipts/finalize.receipt.json'])
write('dossier-manifest.json',{str(p):sha(p) for p in files})
with zipfile.ZipFile('full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[Path('dossier-manifest.json')]:z.write(p,str(p))
write('archive-hashes.json',{n:sha(n) for n in ['source-only-proof.zip','full-dossier.zip']})
print('PASS: frozen inputs, provenance, QA, diagnostics, replay and archives; full entries',len(files)+1)
