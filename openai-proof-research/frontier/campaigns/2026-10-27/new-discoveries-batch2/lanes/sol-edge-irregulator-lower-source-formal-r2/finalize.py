from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).parent
receipt=json.loads((R/'verification-fresh/replay-receipt.json').read_text())
assert receipt['status']=='SOURCE_REFUTATION_REPLAY_PASS'
assert receipt['declaration_count']==136
assert receipt['axiom_union']==['Classical.choice','Quot.sound','propext']
assert all(s['exit']==0 and not s['kill'] for s in receipt['steps'])
packet=R/'edge-irregulator-lower-source-component.zip'
assert hashlib.sha256(packet.read_bytes()).hexdigest()==receipt['archive_sha256']
with zipfile.ZipFile(R/'inherited.zip') as z:
 for m in ['Source','Boundary','Gadget','Edges','Degrees']:
  f='formal/'+m+'.lean'
  assert z.read(f)==(R/'component'/f).read_bytes()==(R/'verification-fresh'/f).read_bytes()
with zipfile.ZipFile(packet) as z:
 assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
 manifest=json.loads(z.read('manifest.json'))
 for n,h in manifest.items():assert hashlib.sha256(z.read(n)).hexdigest()==h
out={'status':receipt['status'],'credit':0,'campaign_accepted_additional':7,'campaign_total':37,
'packet':str(packet.resolve()),'sha256':receipt['archive_sha256'],
'fresh_replay_receipt':str((R/'verification-fresh/replay-receipt.json').resolve()),
'declaration_count':136,'axiom_union':receipt['axiom_union'],
'max_lean_sampled_group_rss_kib':max(s['peak_group_rss_kib'] for s in receipt['steps']),
'new_modules':['Local','Lower','Charges','Transport','Refutation'],
'endpoints':['deletion_card_lower','minimum_lower','minimum_iso','minimum_source_refutation','source_refutation'],
'assigned_source_refutation_residuals':[],
'not_in_scope':['upper witness','exact minimum equality','paper','independent final review','acceptance'],
'failure_and_receipt_limitation':'FAILURES.md'}
(R/'HANDOFF.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
