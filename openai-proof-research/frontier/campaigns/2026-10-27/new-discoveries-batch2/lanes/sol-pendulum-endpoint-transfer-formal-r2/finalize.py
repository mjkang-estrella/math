from pathlib import Path
import json,hashlib,shutil,zipfile,sys
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R))
from audit_tools import audit,sha
dest=R/'extracted-replay'
receipt=json.loads((dest/'replay-receipt.json').read_text())
assert receipt['status']=='MANDATORY_COMPONENT_SOURCE_ONLY_REPLAY_PASS'
assert receipt['declaration_count']==88
assert audit(R)==audit(dest)==receipt['declarations']
manifest=json.loads((R/'manifest.json').read_text())
for f,h in manifest.items():
 assert sha(R/f)==sha(dest/f)==h,f
with zipfile.ZipFile(R/'component-source.zip') as z:
 assert all(not n.endswith(('.olean','.ilean','.ir','.o','.so','.olean.private','.olean.server')) for n in z.namelist())
assert sha(R/'component-source.zip')==sha(R/'component-source-repeat.zip')==receipt['archive_sha256']
f=R.parent/'root-pendulum-moments-adoption-r1/review-freeze.json'
before=json.loads((R/'freeze-before.json').read_text())
assert sha(f)==before['freeze_sha256']
rows=json.loads(f.read_text())['files']
for v in rows:
 p=Path(v['path'])
 assert p.stat().st_size==v['bytes'] and sha(p)==v['sha256'],p
after={'freeze_sha256':sha(f),'entries':len(rows),'mismatches':[],'freeze_itself_unchanged':True,'all_bytes_and_hashes_match':True}
(R/'freeze-after.json').write_text(json.dumps(after,indent=2)+'\n')
shutil.copyfile(dest/'replay-receipt.json',R/'replay-receipt.json')
removed=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and p.name.endswith(('.olean','.ilean','.ir','.o','.so','.olean.private','.olean.server')):
  removed.append(str(p.relative_to(R)))
  p.unlink()
assert not [p for p in R.rglob('*') if p.is_file() and p.name.endswith(('.olean','.ilean','.ir','.o','.so','.olean.private','.olean.server'))]
out={'status':'ENDPOINT_COMPONENT_CLOSED_EXTRACTED_REPLAY_PASS','mathematical_modules':11,'actual_declarations':88,'predecessor_actual_rows_identical':46,'new_actual_declarations':42,'std3_only':True,'all_actual_safety_flags_false':True,'endpoint_integrability_proved':True,'full_literal_closed_interval_continuity_proved':True,'sourceClaim_of_interior_convex_exact_sole_premise':True,'unconditional_source_claim_proved':False,'credit':0,'archive_sha256':sha(R/'component-source.zip'),'manifest_sha256':sha(R/'manifest.json'),'replay_receipt_sha256':sha(R/'replay-receipt.json'),'freeze_before':before,'freeze_after':after,'removed_own_generated_artifacts':removed,'compiled_own_artifacts_remaining':0,'counts_unchanged':'9/39,next40','external_actions':False}
(R/'FINAL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='removed_own_generated_artifacts'},indent=2))
