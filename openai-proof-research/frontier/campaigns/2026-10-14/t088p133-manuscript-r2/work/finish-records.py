from pathlib import Path
import json,hashlib,stat,shutil
R=Path.cwd();P=R/'packet/public';B=R.parent;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
# Local private evidence and cache remain outside public verifier scope.
cache={}
for p in sorted((R/'build/cache').rglob('*')):
 if p.is_file():
  old=B/'t088p133-manuscript-r1'/p.relative_to(R)
  assert h(p)==h(old)
  cache[str(p.relative_to(R))]={'sha256':h(p),'bytes':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'mtime_ns':p.stat().st_mtime_ns,'r1_bytes_mode_mtime_match':p.stat().st_mtime_ns==old.stat().st_mtime_ns and stat.S_IMODE(p.stat().st_mode)==stat.S_IMODE(old.stat().st_mode)}
p=R/'tools/tectonic';old=B/'t088p133-manuscript-r1/tools/tectonic';assert h(p)==h(old)
cache['tools/tectonic']={'sha256':h(p),'bytes':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'mtime_ns':p.stat().st_mtime_ns,'r1_bytes_mode_mtime_match':p.stat().st_mtime_ns==old.stat().st_mtime_ns and stat.S_IMODE(p.stat().st_mode)==stat.S_IMODE(old.stat().st_mode)}
save(R/'private/build-cache-manifest-r2.json',{'scope':'416 named engine/cache files only, no build/work compiler products; outside public verifier','files':cache,'rights':'original upstream tool/cache rights; local private copy only','public_verifier_coverage':False})
# Actual read inventory by named classes; machine metadata is not semantic reading.
read={}
def add(rel,extent):
 p=B/rel;assert p.is_file();read[rel]={'sha256':h(p),'bytes':p.stat().st_size,'extent':extent}
for f in ['main.tex','references.tex','witness-tables.tex','README.md','COVERAGE.md','HANDOFF.md','PROVENANCE.md','RIGHTS.md','build.sh','bootstrap.py','verify.py','support/reproduce.py','support/qa.py','support/integrity_controls.py','support/author-certificate.py','support/geometry_control.py','support/independent_certificate.py','support/certificate-witness.json']:
 add('t088p133-manuscript-r1/packet/public/'+f,'full text; JSON witness decoded all ten rows/all five polynomials/strict subsets' if f.endswith('certificate-witness.json') else 'full text read')
for f in ['REPORT.md','work/notes.md']:add('t088p133-manuscript-r1/'+f,'full text read')
for p in sorted((B/'t088p133-manuscript-r1/packet/public/qa').iterdir()):
 if p.is_file():add(str(p.relative_to(B)),'full retained evidence text/decoded JSON read; historical implementer observation, not new independent QA')
for name in ['t088p133-formal-v1','t088p133-formal-review-r1']:
 for p in sorted((B/name/'packet/public').rglob('*')):
  if p.is_file():add(str(p.relative_to(B)),'full own code/prose/actual type-axiom-control receipts read; inventory/hash metadata authenticated and structurally parsed, not a body-read certificate' if p.name in ['originals-before.json','stable-inputs.json','input-anchors.json','anchors.json'] else 'full code/prose or actual receipt/log read; empty compiler logs checked')
for f in ['assessment.md','contribution-disposition.md','contribution-r1-adoption/adoption.json','proof-r3-disposition.md','proof-r3-adoption/adoption.json','manuscript-r1-intake/intake.json','manuscript-r1-intake/replay.json','manuscript-r1-disposition.md','formal-review-r1-adoption/adoption.json','formal-review-r1-disposition.md','manuscript-formal-integration.md']:add('discovery-analytic-r133-parent/'+f,'full text/decoded JSON read')
for name,files in {'fresh-analytic-discovery-r133':['packet/public/FROZEN-THEOREM.md','packet/public/proof.md','packet/public/certificate.py','packet/public/geometry_control.py','packet/public/reading-limits.md','packet/public/report.md','work/notes.md'],'t088p133-proof-r3':['packet/public/review.md','packet/public/verdict.json','packet/public/independent_certificate.py','packet/public/certificate-witness.json','packet/public/crosscheck.py'],'t088p133-contribution-r1':['packet/public/review.md','packet/public/reading-limits.md']}.items():
 for f in files:add(name+'/'+f,'full text read; duplicate code/witness bytes also authenticated to r1 copies')
save(P/'provenance/implementation-read-record.json',{'stage':'r2 implementation','named_required_read_records':read,'primary_evidence_read_extents':'../../source-reading-records.json from this metadata directory; actual local private files separately bound','limits':'No original manuscript PDF page reinspection claimed; its QA records are historical. R2 PDF has fresh all-page QA. Large inventory JSON authenticated programmatically rather than claiming line-by-line body reading. Output-truncated text reads were repeated in bounded chunks/compact decoded form. No worldwide survey or truth audit.'})
notes='''\nCompleted scoped integration and portable copied-context wrapper: 21/20/15 declarations, actual log bytes identical,10 rational configurations,2 added-premise mutations rejected. No own formal source changes. New PDF first build failed with2 overfull lines in dependency paragraph; hash table and prose wrapping repaired. All20 final120dpi pages individually visually inspected; page14 dense table crop at240dpi confirmed clear spacing. Two final builds on same copied Tectonic/cache gave identical PDF/20PNG bytes. pdftotext bbox contains controls2,3,18,19,20,21: removed only for XML parsing, no PDF/image edit. All text boxes inside pages. Original r1 all17-page QA remains historical; no independent layout/correctness gate. Source preservation: full core through AppendixA unchanged excluding explicit new note;1 theorem,5lemmas,3propositions,9proof environments identical;248terms;11original bib entries identical;53formal public files unchanged. Six original full roots3682entries preserved; six named parent copies match; r1public52/7 and36private namedfiles authenticated separately. Additional broad output truncation of mixed JSON/log reads was corrected by compact full JSON printing. No new download; no browser/git/nestedagent/publication.\n'''
with (R/'work/notes.md').open('a') as f:f.write(notes)
print(json.dumps({'cache_and_engine_files':len(cache),'all_copied_metadata_matches':all(x['r1_bytes_mode_mtime_match'] for x in cache.values()),'named_read_records':len(read)}))
