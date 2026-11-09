from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
p=L/'freeze.json';d=json.loads(p.read_text());(L/'freeze-before-admin-repair.json').write_bytes(p.read_bytes())
for i,r in enumerate(d['references']):
 if r['kind']!='administrative-snapshot':continue
 original=Path(r['original']);data=original.read_bytes()
 assert hashlib.sha256(data).hexdigest()==r['sha256'],'Cannot recreate initial snapshot after original change'
 q=L/'administrative'/str(i)/original.name;q.parent.mkdir(exist_ok=True);q.write_bytes(data);r['copy']=str(q)
d['administrative_repair']=dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='Duplicate AGENTS.md basename collided; unique administrative paths restored from unchanged originals; scientific references unaffected')
p.write_text(json.dumps(d,indent=2))
with (L/'FAILURES.md').open('a') as f:f.write('\n7. First finalize invocation failed because two administrative AGENTS.md snapshots shared a basename. freeze-before-admin-repair.json preserves the original metadata. repair_admin.py restored unique snapshot paths only after verifying each administrative original still matched its recorded initial hash. Scientific freezes were unaffected. Failed guard exit1 retained in finalization-failure.json.\n')
(L/'finalization-failure.json').write_text(json.dumps(dict(script='finalize.py',exit=1,error='administrative snapshot basename collision; assertion on copy digest',scientific_source_changed=False),indent=2))
