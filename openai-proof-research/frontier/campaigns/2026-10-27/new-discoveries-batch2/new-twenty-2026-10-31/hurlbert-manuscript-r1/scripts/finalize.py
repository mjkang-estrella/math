from pathlib import Path
import json,hashlib,zipfile,platform,sys,re,shutil
D=Path(__file__).resolve().parents[1];P=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((D/'receipts/inputs-before.json').read_text());after={rel:sha(P/rel) for rel in before};assert before==after
assert all(sha(D/'inputs'/rel)==h for rel,h in before.items())
(D/'receipts/inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
raw=D/'inputs/expanded-corpus-r234/raw/356266.jsonl';shutil.copyfile(raw,D/'356266.jsonl');assert raw.read_bytes().endswith(b'\n')
(D/'receipts/raw-line.json').write_text(json.dumps(dict(path='356266.jsonl',sha256=sha(raw),bytes=raw.stat().st_size,newline_preserved=True),indent=2)+'\n')
assert sha(D/'proof-source.zip')=='d695606abe9bdcd465c1b0de182bc8e9c202044720687c92adcd8ff7314192e6'
r=json.loads((D/'recomputed.json').read_text());old=json.loads((D/'inputs/hurlbert-review-r1/mathematics.json').read_text())
assert r['exhaustive']['3']==[old['3']['exhaustive_fixed_first_edge'],old['3']['nonrealizable']]
assert r['review_search']['failures']==old['4']['nonrealizable'] and r['review_search']['trials']==old['4']['trials']
aw=json.loads((D/'inputs/hurlbert-review-r1/albert-west-augmentation.json').read_text());assert aw['tested']==r['albert_west']['tested'] and aw['found'] is None
parent=json.loads((D/'inputs/hurlbert-parent-final-r1/replay-result.json').read_text());assert parent['verdict']=='PASS'
assert parent['packet_sha256']==sha(D/'proof-source.zip')
metadata=dict(numerical_results='recomputed.json; fresh scripts/recompute.py',literal_parameters={'n':len(r['witness'][0])-1,'N':len(r['witness'])-1},lean_version=parent['lean'],module_names=list(parent['modules']),bibliographic_metadata='Frozen primary texts, source bibliography and reviewer citation metadata; historical years, pages, section identifiers, DOIs and hashes are identifiers, not experimental counts.',document_number_tokens=re.findall(r'\d+(?:[.,]\d+)*',(D/'manuscript.md').read_text()))
assert metadata['literal_parameters']=={'n':3,'N':23}
(D/'receipts/numbers.json').write_text(json.dumps(metadata,indent=2)+'\n')
(D/'receipts/environment.json').write_text(json.dumps(dict(python=sys.version,platform=platform.platform(),network=False,lean_executed=False,solvers_executed=False),indent=2)+'\n')
(D/'receipts/authoring-history.json').write_text(json.dumps(dict(initial_system_python_reportlab_missing=True,resolved_with_existing_local_runtime=True,initial_layout_overflow=True,corrected_heading_parser=True,final_pages=6,no_installation=True),indent=2)+'\n')
results=dict(mathdb_id=356266,status='DRAFT_READY_FOR_ROOT_REVIEW',accepted=False,accepted_credit=0,ai_assistance='OpenAI Codex',paper='manuscript.pdf',source=['manuscript.md','scripts/render.py'],pages=6,packet_sha256=sha(D/'proof-source.zip'),frozen_inputs_unchanged=True,formal_replay='Supplied parent PASS, no Lean run in this lane',registry_screen='Supplied parent CLEAN, path screens only',fresh_computations=r,limitations=['Thesis body unread','Jackson body unread','CDG citing-work title screen only','Folklore not excluded','No priority claim'])
(D/'results.json').write_text(json.dumps(results,indent=2)+'\n')
# Remove obsolete overflow images; the final six images were individually inspected.
for p in (D/'qa').glob('page-*.png'):
 if int(p.stem.split('-')[-1])>6:p.unlink()
(D/'receipts/visual-qa.json').write_text(json.dumps(dict(status='PASS',method='Rendered every final page with Poppler and visually inspected each PNG through view_image; checked text, math glyphs, both tables, spacing, footer and page boundaries',pages=[dict(page=i,image=f'qa/page-{i}.png',sha256=sha(D/f'qa/page-{i}.png'),inspected=True) for i in range(1,7)],paper_sha256=sha(D/'manuscript.pdf')),indent=2)+'\n')
excluded={'manifest.sha256','full-dossier.zip','archive.sha256','receipts/package.json','receipts/finalize.json'}
files=sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in excluded and 'tmp' not in p.relative_to(D).parts)
(D/'manifest.sha256').write_text(''.join(f'{sha(p)}  {p.relative_to(D)}\n' for p in files))
files.append(D/'manifest.sha256')
with zipfile.ZipFile(D/'full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files:z.write(p,str(p.relative_to(D)))
with zipfile.ZipFile(D/'full-dossier.zip') as z:
 assert z.testzip() is None
 assert len(z.namelist())==len(set(z.namelist()))==len(files)
 for p in files:assert hashlib.sha256(z.read(str(p.relative_to(D)))).hexdigest()==sha(p)
(D/'archive.sha256').write_text(f'{sha(D/"full-dossier.zip")}  full-dossier.zip\n')
(D/'receipts/package.json').write_text(json.dumps(dict(zip_integrity='PASS',member_hashes='PASS',safe_relative_names=True,files=len(files),archive_sha256=sha(D/'full-dossier.zip'),frozen_input_count=len(before),frozen_inputs_unchanged=True),indent=2)+'\n')
print('DRAFT packaged; hashes and ZIP verified; root acceptance pending.')
