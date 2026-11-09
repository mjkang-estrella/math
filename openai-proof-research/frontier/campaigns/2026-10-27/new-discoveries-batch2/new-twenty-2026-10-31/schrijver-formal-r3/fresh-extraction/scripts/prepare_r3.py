from pathlib import Path
import json,hashlib,subprocess,sys
r=Path(__file__).resolve().parent.parent
p=r/'src/TableLinks.lean.tmp'
if p.exists():p.unlink()
subprocess.run([sys.executable,'-I',str(r/'scripts/audit_r3.py')],check=True)
old=json.loads((r.parent/'schrijver-formal-r2/outputs/modules.json').read_text())
mods=old+['TableLinks','MetricTransport']+json.loads((r/'outputs/table-modules.json').read_text())+['UpperTrees','BridgeTransport','ClosureAudit','AuditR3']
assert set(mods)=={p.stem for p in (r/'src').glob('*.lean')}
(r/'outputs/modules.json').write_text(json.dumps(mods,indent=2))
# Include immutable inherited hash receipts in the source manifest and zip.
for n in ['frozen-before.json','frozen-after.json','inputs-read.json']:
 (r/'outputs'/n).write_bytes((r/n).read_bytes())
subprocess.run([sys.executable,'-I',str(r/'scripts/package.py')],check=True)
