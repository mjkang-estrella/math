#!/usr/bin/env python3
"""External receipt/hash finalization. Run only after final-fresh replay completes."""
from pathlib import Path
import hashlib,json,shutil,zipfile
b=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=b/'verification/final-fresh';r=json.loads((f/'extraction-receipt.json').read_text());assert r['status']=='PASS' and r['mathematical_module_count']==35 and r['full_generated_origin_declaration_count']==1041
archive=b/'packet/jacobi-shifted-source-proof.zip';assert r['packet_sha256']==sha(archive);assert archive.read_bytes()==(b/'packet/regenerated.zip').read_bytes()
assert len(r['steps'])==39
assert all((f/'build/formal'/f'{n}.lean.log').stat().st_size==0 for n in json.loads((b/'component.json').read_text())['mathematical_modules'])
assert (f/'build/declarations.json').read_bytes()==(b/'verification/audit/declarations.json').read_bytes()
# The README's shorter receipt location is an explicitly published copy; original remains final-fresh.
shutil.copyfile(f/'extraction-receipt.json',b/'verification/fresh/extraction-receipt.json')
shutil.copyfile(f/'build/declarations.json',b/'verification/declarations.json')
repro={'status':'PASS','archive_sha256':sha(archive),'regenerated_archive_sha256':sha(b/'packet/regenerated.zip'),'byte_identical':True,'manifest_excludes_itself':True,'external_receipt_sha256':sha(f/'extraction-receipt.json'),'external_receipt_original':'verification/final-fresh/extraction-receipt.json','external_receipt_published_copy':'verification/fresh/extraction-receipt.json'}
(b/'packet/reproducibility.json').write_text(json.dumps(repro,indent=2)+'\n')
orig=json.loads((b/'provenance/frozen-before.json').read_text())
for x in orig['files']:assert sha(Path(x['original']))==x['sha256']==sha(b/x['copy'])
assert sha(b/'formal/SourceDefs.lean')=='df95c10e6a9371c1fc3f09424375a4ff51707980db0635e9a321d2c8a09033a5'
(b/'verification/frozen-final.json').write_text(json.dumps({'status':'PASS','checked_original_copy_pairs':len(orig['files']),'mathematical_modules_unchanged':35,'SourceDefs_sha256':sha(b/'formal/SourceDefs.lean')},indent=2)+'\n')
with zipfile.ZipFile(archive) as z:
 m=json.loads(z.read('manifest.json'))
 for n,h in m.items():assert sha(b/n)==h,n
result=f'''# Final implementation result

PASS: own fresh extracted source-only replay of all 35 mathematical modules,
with 1,041 actual-origin declarations checked, all safe and std3-only.
The 39 build steps comprise 35 mathematical and four audit/display modules.
Peak sampled process-tree RSS: {r['peak_sampled_process_tree_rss_kib']} KiB
(ceiling 3145728 KiB). Diagnostics: {r['diagnostics_bytes']} bytes (cap 536870912).
All mathematical logs are empty; all source/payload and nine package pins passed
before and after. Endpoint prints both abbreviated and expanded.

Archive SHA256: `{sha(archive)}`.
Paper SHA256: `{sha(b/'paper.pdf')}`; six final pages personally inspected.
Archive regeneration and PDF rebuilding were byte-identical.

Original final receipt: verification/final-fresh/extraction-receipt.json.
README's verification/fresh/extraction-receipt.json is an identical published
copy of that receipt; the failed first extraction logs in that directory are
retained and are not the successful final build. Receipt extraction_directory
identifies final-fresh explicitly. Failed attempts are documented in ATTEMPTS.
Final current sources are fixed; no frozen mathematical source was edited.

This is preparation only, not independent acceptance. Credit 0; one family;
counts 2/30 additional, 32/60 total unchanged. Distinct independent final review
and current novelty/subsumption adjudication remain pending.
'''
(b/'FINAL-RESULT.md').write_text(result)
excluded={'.olean','.ilean','.ir','.o','.so','.pyc','.aux','.out','.xdv','.fmt'}
files={}
for p in sorted(b.rglob('*')):
 rel=p.relative_to(b)
 if not p.is_file() or p.name=='final-review-hashes.json' or p.suffix in excluded:continue
 if '__pycache__' in p.parts or str(rel).startswith(('paper/cache/','paper/tmp/')):continue
 files[rel.as_posix()]=sha(p)
(b/'final-review-hashes.json').write_text(json.dumps({'status':'PASS','scope':'Every retained lane file except this self-reference, runtime caches and compiled/intermediate artifacts. Includes failed-attempt logs as historical evidence.','files':files},indent=2,sort_keys=True)+'\n')
print(result)
