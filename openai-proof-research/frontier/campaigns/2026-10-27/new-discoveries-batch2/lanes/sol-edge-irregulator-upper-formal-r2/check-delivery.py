import json,hashlib,zipfile
from pathlib import Path
r=Path(__file__).parent
receipt=json.loads((r/'verification-fresh/replay-receipt.json').read_text())
h=hashlib.sha256((r/'upper-witness-component.zip').read_bytes()).hexdigest()
assert receipt['status']=='UPPER_WITNESS_REPLAY_PASS' and receipt['archive_sha256']==h
assert receipt['declaration_count']==117 and receipt['initial_own_prebuilt_artifacts']==0
assert receipt['axiom_union']==['Classical.choice','Quot.sound','propext']
print(json.dumps({'archive_sha256':h,'status':receipt['status'],'declarations':117,'peak_lean_group_rss_kib':max(s['peak_group_rss_kib'] for s in receipt['steps'])},indent=2))
