import pathlib,json,zipfile,re
from audit_tools import sha,audit,dependencies,MODS
R=pathlib.Path(__file__).resolve().parent
rows=audit(R)
(R/'actual-declarations.json').write_text(json.dumps(rows,indent=2)+'\n')
(R/'dependency-hashes.json').write_text(json.dumps(dependencies(R),indent=2)+'\n')
files=['guard.py','helper_guard.py','replay_guard.py','pins.json','originals-before.json','input-records.json','verify_inputs.py','audit_tools.py','replay.py','package.py','SUMMARY.md','dependency-hashes.json','actual-declarations.json']
files += [str(p.relative_to(R)) for p in sorted((R/'inputs').iterdir())]
files += ['formal/'+m+'.lean' for m in MODS+['FullAudit']]
for m in MODS:
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial|implemented_by)\b',(R/'formal'/f'{m}.lean').read_text())
manifest={f:sha(R/f) for f in sorted(files)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
files.append('manifest.json')
def pack(dest):
 with zipfile.ZipFile(dest,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for f in sorted(files):
   info=zipfile.ZipInfo(f,(2026,10,29,0,0,0));info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
   z.writestr(info,(R/f).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
pack(R/'component-source.zip');pack(R/'component-source-repeat.zip')
assert sha(R/'component-source.zip')==sha(R/'component-source-repeat.zip')
receipt={'component_mandatory_proofs_closed':True,'full_source_claim_proved':False,'credit':0,'modules':MODS,'declarations':len(rows),'archive_sha256':sha(R/'component-source.zip'),'dependency_files':len(dependencies(R)),'deterministic_repeat_identical':True}
(R/'archive-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
