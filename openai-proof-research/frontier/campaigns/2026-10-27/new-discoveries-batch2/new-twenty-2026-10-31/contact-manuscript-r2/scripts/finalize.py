from pathlib import Path,PurePosixPath
import hashlib,json,shutil,zipfile,re,stat
lane=Path(__file__).resolve().parent.parent;b=lane.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def copy(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 if src.is_dir():shutil.copytree(src,dst,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.olean','*.ilean','*.ir'))
 else:shutil.copy2(src,dst)
# Preserve current evidence separately from historical dossier claims.
for x in ['sources','evidence']:
 copy(b/'contact-manuscript-r1'/x,lane/('sources' if x=='sources' else 'historical-r1/evidence'))
for x in ['DOSSIER-MANIFEST.json','REPRODUCE.md']:
 copy(b/'contact-manuscript-r1'/x,lane/'historical-r1'/x)
(lane/'historical-r1/README.md').write_text('HISTORICAL r1/r5 evidence only. Old predicates, endpoints, source archives and replay claims here are superseded by the operative r6 packet. Retained for source provenance and bounded prior-art history; no historical replay is presented as the repaired replay.\n')
for x in ['STATEMENT-CORRESPONDENCE.md','REGRESSION.md','SUMMARY.md','results.json','REPRODUCE.md','scripts','formal','fresh-extraction/replay-logs']:
 copy(b/'contact-formal-r6'/x,lane/'evidence/r6'/x)
# Additional exact-algebra log is evidence only, never re-executed.
extra=b/'contact-formal-r6/logs/regression-final.log'
dump(lane/'qa/supplementary-inputs-before.json',{str(extra.relative_to(b)):H(extra)})
copy(extra,lane/'evidence/r6/logs/regression-final.log')
for x in ['contact-review-r3','contact-review-r2']:
 for f in ['REVIEW.md','review.json']:copy(b/x/f,lane/'reviews'/x/f)
copy(b/'contact-review-r3/logs',lane/'reviews/contact-review-r3/logs')
copy(b/'contact-root-ruling-r2.json',lane/'reviews/contact-root-ruling-r2.json')
# Structural and evidence checks, no Lean execution.
sha='e92d6eceaf79972064c2f142a9cd1c4b3df45b520d1eed0445f288cddc1270d6'
assert H(lane/'contact-source-only.zip')==sha
assert (lane/'contact-source-only.zip').read_bytes()==(b/'contact-formal-r6/contact-r6-source.zip').read_bytes()
with zipfile.ZipFile(lane/'contact-source-only.zip') as z,zipfile.ZipFile(b/'contact-manuscript-r1/evidence/contact-r5-source.zip') as old:
 def safe(i):
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and not stat.S_ISLNK(i.external_attr>>16)
 for i in z.infolist():safe(i)
 modules=[n for n in z.namelist() if n.startswith('formal/') and n.endswith('.lean')]
 assert len(modules)==33
 for n in modules: assert z.read(n)==(b/'contact-formal-r6'/n).read_bytes()
 hist=[n for n in old.namelist() if n.startswith('formal/') and n.endswith('.lean')]
 assert len(hist)==28
 for n in hist: assert z.read(n)==old.read(n)
 dump(lane/'qa/source-archive.json',{'sha256':sha,'byte_identical_to_r6':True,'safe_paths':True,'modules':len(modules),'historical_modules_byte_identical':len(hist),'compiled_artifacts':False})
rp=lane/'evidence/r6/fresh-extraction/replay-logs'
complete=json.loads((rp/'complete.json').read_text());inv=json.loads((rp/'audit-inventory.json').read_text());neg=json.loads((rp/'negative-controls-reviewed.json').read_text())
assert complete['status']=='PASS' and complete['modules']==33 and complete['negative_controls']==17
assert len(neg['controls'])==17
for n,h in complete['source_sha256'].items():assert H(lane/'evidence/r6/formal'/n)==h
allowed={'propext','Classical.choice','Quot.sound'}; ax={}
for d in inv['declarations']:
 if d['name'] in ['ContactPilot.refutationLocal','ContactPilot.local_contact_unique','ContactPilot.bidisk_local_contact_six']:
  assert set(d['axioms'])<=allowed;ax[d['name']]=d['axioms']
assert len(ax)==3
for n in neg['controls']:
 receipt=json.loads((rp/(n+'.receipt.json')).read_text());assert receipt['returncode']==1 and receipt['killed'] is None
assert len(list(rp.glob('checker-*.log.receipt.json')))==33
assert len(list(rp.glob('lean-*.log.receipt.json')))==33
# Preserve graph, jets, source numbering, related work and bibliography verbatim.
s=(lane/'paper/contact-draft.md').read_text();old=(b/'contact-manuscript-r1/paper/contact-draft.md').read_text()
def section(t,k):
 a=t.index('## '+str(k)+'.');n=t.find('\n## ',a+1)
 return t[a:n if n!=-1 else len(t)].replace('---PAGE---','').strip()
unchanged={str(k):section(s,k)==section(old,k) for k in [2,3,8,9]};assert all(unchanged.values())
assert H(lane/'paper/build_paper.py')==H(b/'contact-manuscript-r1/paper/build_paper.py')
dump(lane/'qa/preserved-content.json',{'sections_unchanged':unchanged,'build_paper_byte_identical':True,'genuine_errors_found':[]})
patterns=['refutation :','SourceConjecture ','HasZeroSetContact','28 modules','13 negative']
grep={}
for f in ['paper/contact-draft.md','qa/contact-draft.txt','PROOF.md','STATEMENT-CORRESPONDENCE.md']:
 t=(lane/f).read_text();grep[f]={p:[{'line':i,'text':l} for i,l in enumerate(t.splitlines(),1) if p in l] for p in patterns}
 assert not grep[f]['refutation :'] and not grep[f]['SourceConjecture '] and not grep[f]['28 modules'] and not grep[f]['13 negative']
 assert all('HISTORICAL' in x['text'] for x in grep[f]['HasZeroSetContact'])
dump(lane/'qa/grep.json',grep)
(lane/'qa/grep.md').write_text('Checked Markdown, PDF extracted text, PROOF and STATEMENT-CORRESPONDENCE for all five required literal patterns. No stale operative endpoint/count claims. The sole HasZeroSetContact occurrence in each document is explicitly HISTORICAL. The historical SourceConjecture name is parenthesized within that historical paragraph. See grep.json for exact lines.\n')
texts=(lane/'qa/contact-draft.txt').read_text().split('\f');texts=[t for t in texts if t.strip()];assert len(texts)==10
notes=['Exact local quantifiers and repaired abstract; no clipping.','Graph, matrix and reduction unchanged; matrix aligned.','Branch jets and level comparisons unchanged and legible.','Arbitrary-neighborhood half-plane attribution and constants legible.','Bidisk constants and every-rho clause; no symbol defects.','Local universal endpoint, table and operative chain checked.','Existence versus uniqueness bridge and historical defect checked.','Diagnostic order-2 proof and non-Lean status checked.','33-module packet, 17 controls, pending root replay and trust limits checked.','Bounded prior-art and bibliography unchanged, citations legible.']
dump(lane/'qa/page-checks.json',{'pdf_sha256':H(lane/'paper/contact-draft.pdf'),'page_count':10,'method':'Every page read as rendered PNG and extracted text; changed pages 4,6,9 reread after final attribution correction.','layout':'No clipping, overlap, missing glyphs or footer collisions observed.','pages':[{'page':i+1,'image':f'page-{i+1:02}.png','image_sha256':H(lane/'qa'/f'page-{i+1:02}.png'),'text_sha256':hashlib.sha256(t.encode()).hexdigest(),'check':notes[i]} for i,t in enumerate(texts)]})
dump(lane/'qa/r6-evidence-checks.json',{'supplied_not_rerun':True,'modules':33,'checker_receipts':33,'negative_controls':17,'negative_receipts_exit_one_no_kill':True,'source_hashes_match_complete':True,'declaration_count':inv['declaration_count'],'endpoint_axioms':ax,'root_decisive_replay':'PENDING'})
# Rehash all named inputs.
before=json.loads((lane/'inputs-before.json').read_text());after={}
for rel in json.loads((lane/'scripts/input_paths.json').read_text()):
 p=b/rel
 for f in sorted(p.rglob('*')) if p.is_dir() else [p]:
  if f.is_file():after[str(f.relative_to(b))]={'sha256':H(f),'bytes':f.stat().st_size}
dump(lane/'inputs-after.json',after);assert before==after
dump(lane/'qa/input-verification.json',{'files':len(before),'identical':True,'before_sha256':H(lane/'inputs-before.json'),'after_sha256':H(lane/'inputs-after.json')})
dump(lane/'qa/supplementary-inputs-after.json',{str(extra.relative_to(b)):H(extra)})
assert (lane/'qa/supplementary-inputs-before.json').read_bytes()==(lane/'qa/supplementary-inputs-after.json').read_bytes()
(lane/'REPRODUCE.md').write_text('''# Reproduce the repaired r6 packet

contact-source-only.zip is byte-identical to contact-formal-r6/contact-r6-source.zip, SHA-256 e92d6eceaf79972064c2f142a9cd1c4b3df45b520d1eed0445f288cddc1270d6. Verify this hash first. Extract into a NEW empty directory, rejecting absolute paths, parent traversal, backslashes and symbolic links. Check SOURCE-MANIFEST.json if present and every source hash against the delivered manifest. Never use the historical r5 driver as the repaired certificate.

For a separately authorized replay, follow evidence/r6/REPRODUCE.md: set LEAN_BIN to the executable for Lean 4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52), LEAN_PACKAGES to the read-only package cache pinned to mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, then run `python3 -I -B scripts/replay-r6.py` from that new extraction. The r6 driver runs 33 serial strict builds/checkers, audits declaration DAGs/axioms and requires 17 negative controls to fail correctly. Its caps and dependency trust limits are in its REPRODUCE.md. This manuscript lane did NOT run Lean or lake. Root's decisive fresh replay remains pending.

For the paper, the copied paper/build_paper.py is byte-identical to r1. With ReportLab available to isolated Python, use `python3 -I scripts/capped.py logs/rebuild.log python3 -I -B paper/build_paper.py`. This environment required lane-local copies of existing ReportLab dependencies: scripts/build_isolated.py adds tmp/pdf-deps explicitly and executes the unchanged builder using runpy; run it via the same capped command instead. qa/pdf-dependencies.json records hashes and the read-only origin. No installation or network was used. Fonts are Liberation Serif/Mono under /usr/share/fonts. The dependency copy is not bundled in the dossier; supply ReportLab in your own isolated environment to reproduce. Render using the capped pdftoppm invocation in logs/render-sealed.log.receipt.json. Review all ten pages and the required pattern checks recorded in qa/.

DOSSIER-MANIFEST.json hashes every full-dossier member except itself. results.json records final archive hashes outside the archive to avoid circular hashes. Historical r1 evidence is labeled in historical-r1/README.md. No historical acceptance or replay is promoted to the operative r6 endpoint. Root alone decides acceptance; credit stays zero.
''')
changes=[{'gate_D':1,'files':['paper/contact-draft.md','PROOF.md','STATEMENT-CORRESPONDENCE.md'],'change':'Exact fixed c,C,rho0 quantifiers, every-rho witnesses and local endpoint abstract.'},{'gate_D':2,'files':['paper/contact-draft.md','PROOF.md'],'change':'half_plane_contact_six_localized attributed; weaker half-plane predicate HISTORICAL.'},{'gate_D':3,'files':['paper/contact-draft.md','PROOF.md'],'change':'Local contact six with verified rho0=1/2,c=1/512,C=16; uniqueness and exclusion.'},{'gate_D':4,'files':['paper/contact-draft.md','PROOF.md','STATEMENT-CORRESPONDENCE.md'],'change':'SourceConjectureLocal/refutationLocal, table and operative chain; lower provenance; existence bridge, historical defect and ordinary diagnostic regression.'},{'gate_D':5,'files':['paper/contact-draft.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md'],'change':'33-module r6 archive/hash, 28 unchanged historical modules, evidence-bound 17 controls and repaired endpoint axiom checks; root fresh replay pending.'},{'gate_D':6,'files':['paper/contact-draft.pdf','qa','contact-source-only.zip','contact-full-dossier.zip','DOSSIER-MANIFEST.json'],'change':'PDF regenerated and every page read; dossier rebound to r6; graph/jet/related-work/bibliography sections and builder preserved.'}]
limits=['Root decisive fresh replay and acceptance pending; no self-acceptance or count increment.','No Lean or lake run in this lane. Supplied r6 replay and bounded r3 review are distinct evidence.','General source-contact existence bridge and diagnostic regression are ordinary arguments, not general Lean existence/diagnostic theorems.','Cached dependency binaries trusted; no dependency-source rebuild.','No new novelty or priority clearance; inherited unread-source/access limits retained.']
result={'mathdb_id':365301,'lane':lane.name,'status':'MANUSCRIPT_INTEGRATION_COMPLETE_PENDING_ROOT','accepted_credit':0,'campaign_count_unchanged':'22/40 beyond 39','root_decides':True,'changes_by_gate_D':changes,'pdf_pages':10,'all_pages_read':True,'input_files_hash_bound':len(before),'input_hashes_unchanged':True,'r6_source_sha256':sha,'historical_modules_unchanged':28,'r6_modules':33,'supplied_r6_negative_controls':17,'residual_limits':limits,'genuine_errors_outside_repair_found':[],'initial_build_failure':'Isolated Python lacked ReportLab; retained logs/build.log; copied existing dependencies lane-locally and executed unchanged builder via isolated runpy wrapper.','no_background_jobs':True,'artifacts':{}}
dump(lane/'results.json',result)
(lane/'SUMMARY.md').write_text('''# MathDB 365301 manuscript integration r2

All six gate-D manuscript items are integrated in paper/contact-draft.md, PROOF.md and STATEMENT-CORRESPONDENCE.md as applicable. The operative endpoint is ContactPilot.refutationLocal, negating SourceConjectureLocal. The exact local quantifier order, fixed constants, arbitrary-function uniqueness, ordinary source-existence bridge, historical locality failure and diagnostic local order 2 are explicit.

The PDF was regenerated with the unchanged copied builder under isolated Python and resource caps. All 10 pages were read as rendered images and text; changed pages were reread after final attribution edits. No clipping, overlaps or missing symbols were observed. qa/ retains images, extracted text, exact required grep checks, page receipts and evidence checks. Sections 2,3,8,9 are verbatim preserved. The initial missing-ReportLab failure and successful lane-local dependency workaround are logged.

contact-source-only.zip is byte-identical to the r6 archive, SHA-256 e92d6eceaf79972064c2f142a9cd1c4b3df45b520d1eed0445f288cddc1270d6. Its 33 modules match r6; 28 historical modules match the preserved r5 archive. contact-full-dossier.zip includes the revised paper/source, proof/correspondence, regression, reviews, source receipts, r6 replay records and DOSSIER-MANIFEST.json. Historical r1/r5 evidence is explicitly labeled. results.json maps every change to gate D and records final hashes. All 890 named input files are unchanged under before/after SHA-256 manifests.

No Lean or lake, child agents, git, network, browser tabs, external messages, uploads or shared-ledger edits were used. All writes and temporary/cache paths stayed in this lane. Heavy processes were serial with two-CPU affinity, CPU 120 s, wall 140 s, sampled total group RSS about 6 GiB and MALLOC_ARENA_MAX=2; no cap kill or background job remains.

Root's decisive fresh replay is PENDING and is not claimed. Supplied r6 full-replay evidence and r3's bounded closure check are distinguished. The diagnostic and general existence correspondence remain ordinary arguments. Cached dependency binaries and inherited novelty/access limits remain. Integration is not acceptance: root decides; credit is zero and count remains 22/40 beyond 39.
''')
# Bind a finite dossier payload. results.json stays external because it hashes the archive.
roots=['paper','PROOF.md','STATEMENT-CORRESPONDENCE.md','REGRESSION.md','REPRODUCE.md','SUMMARY.md','contact-source-only.zip','sources','historical-r1','evidence','reviews','qa','inputs-before.json','inputs-after.json','scripts','logs']
files=[]
for root in roots:
 p=lane/root
 files.extend([f for f in p.rglob('*') if f.is_file()] if p.is_dir() else [p])
files=[p for p in files if p.name not in ['seal.log','seal.log.receipt.json']]
assert not any(p.suffix in ['.olean','.ilean','.ir','.pyc'] for p in files)
manifest={'scope':'All dossier members except DOSSIER-MANIFEST.json itself; external results.json hashes the archive.','files':{str(p.relative_to(lane)):{'sha256':H(p),'bytes':p.stat().st_size} for p in sorted(files)}}
dump(lane/'DOSSIER-MANIFEST.json',manifest)
with zipfile.ZipFile(lane/'contact-full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in sorted(files+[lane/'DOSSIER-MANIFEST.json']):
  rel=str(p.relative_to(lane)); assert '..' not in PurePosixPath(rel).parts and not p.is_symlink();z.write(p,rel)
with zipfile.ZipFile(lane/'contact-full-dossier.zip') as z:
 assert z.testzip() is None
 for rel,v in manifest['files'].items():assert hashlib.sha256(z.read(rel)).hexdigest()==v['sha256']
 assert json.loads(z.read('DOSSIER-MANIFEST.json'))==manifest
result['artifacts']={f:{'sha256':H(lane/f),'bytes':(lane/f).stat().st_size} for f in ['paper/contact-draft.pdf','paper/contact-draft.md','paper/build_paper.py','PROOF.md','STATEMENT-CORRESPONDENCE.md','REGRESSION.md','REPRODUCE.md','SUMMARY.md','DOSSIER-MANIFEST.json','contact-source-only.zip','contact-full-dossier.zip','inputs-before.json','inputs-after.json']}
result['dossier_manifest_members']=len(manifest['files']);result['dossier_verified']=True
dump(lane/'results.json',result)
print(json.dumps({'status':result['status'],'inputs_unchanged':len(before),'dossier_files':len(manifest['files']),'archive_sha256':result['artifacts']['contact-full-dossier.zip']['sha256']}))
