import pathlib,json,hashlib,zipfile,sys,shutil
R=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(R))
from audit_tools import sha,audit,dependencies,MODS
ex=R/'EXTRACTED'
receipt=json.loads((ex/'replay-receipt.json').read_text())
assert receipt['status']=='MANDATORY_COMPONENT_SOURCE_ONLY_REPLAY_PASS'
assert receipt['archive_sha256']==sha(R/'component-source.zip')==sha(R/'component-source-repeat.zip')
assert receipt['declaration_count']==96
assert receipt['initial_own_prebuilt_artifacts']==0
assert receipt['source_claim_pass'] is False and receipt['credit']==0
assert audit(R)==audit(ex)==receipt['declarations']
assert dependencies(R)==dependencies(ex)
assert all(row['exit']==0 and row['kill'] is None for row in receipt['steps'])
assert all(row['peak_group_rss_kib']<=2800*1024 for row in receipt['steps'])
before=json.loads((R/'freeze-before.json').read_text())
freeze=R.parent/'root-pendulum-moments-adoption-r1/review-freeze.json'
assert sha(freeze)==before['freeze_sha256']
frozen=json.loads(freeze.read_text())['files']
for row in frozen:
 p=pathlib.Path(row['path'])
 assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
for f,h in json.loads((R/'manifest.json').read_text()).items():
 assert sha(R/f)==h
 assert sha(ex/f)==h
with zipfile.ZipFile(R/'component-source.zip') as z:
 assert not any(n.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc')) for n in z.namelist())
p=R.parent/'sol-pendulum-source-moments-formal-r1'
for m in MODS[:4]:
 assert (R/'formal'/f'{m}.lean').read_bytes()==(p/'formal'/f'{m}.lean').read_bytes()
old=json.loads((p/'actual-declarations.json').read_text())
assert [x for x in receipt['declarations'] if x['origin'] in MODS[:4]]==old
shutil.copyfile(ex/'replay-receipt.json',R/'replay-receipt.json')
out={'status':'ALL_ASSIGNED_INTERIOR_OBLIGATIONS_CLOSED_REPLAY_PASS',
 'credit':0,'counts_unchanged':[9,39,40],'full_SourceClaim_proved':False,
 'modules':MODS,'actual_declarations':96,'inherited_declarations_unchanged':46,
 'new_declarations':50,'upstream_dependency_files_hashed':len(dependencies(R)),
 'archive_sha256':sha(R/'component-source.zip'),'replay_receipt_sha256':sha(R/'replay-receipt.json'),
 'freeze_before_after_sha256':sha(freeze),'freeze_payload_entries_verified':len(frozen),
 'zero_own_prebuilt_inputs':True,'deterministic_archive_repeat':True,
 'all_steps_pass':True,'maximum_sampled_lean_group_rss_kib':max(x['peak_group_rss_kib'] for x in receipt['steps']),
 'process_qualification':'Initial unguarded pwd, ls and helper-guard bootstrap read; see PROVENANCE.json. No caps raised.',
 'residuals':['Separately assigned literal endpoint continuity and closed transfer','Historical acceptance gaps and final independent review/paper/acceptance; no credit']}
(R/'FINAL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
