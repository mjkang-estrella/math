"""Create the first I80 gap-report evidence seal, once, after a successful replay.
This is a development write operation, never part of read-only verification.
A held nomination is deliberately not promoted by a successful evidence replay.
"""
from pathlib import Path
import subprocess,sys,json,hashlib,datetime,os
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i80_geometric_flows_computation_discovery';E=Path(__file__).resolve().parent
seal=S/'seal-v1.json'
if seal.exists():raise SystemExit('Refusing to reseal an existing immutable report.')
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
p=subprocess.run([sys.executable,'-B',str(E/'verify.py'),'--preseal'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env)
record=S/'development/preseal-final.json'
if record.exists():raise SystemExit('Refusing to overwrite a retained final pre-seal run.')
record.write_bytes(p.stdout)
if p.returncode:
 (S/'development/preseal-final.stderr').write_bytes(p.stderr)
 raise SystemExit('Pre-seal failure retained. No seal created.')
x=json.loads(p.stdout)
if x['status']!='PASS_EVIDENCE_ONLY':raise SystemExit('Unexpected replay status; no seal created.')
files=sorted([R/'frontier/iterations/i80-geometric-flows-computation-discovery.md']+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=seal],key=lambda p:str(p.relative_to(R)))
entries=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in files]
data=dict(schema='I80-evidence-seal-v1',pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Immutable research gap snapshot. Nomination held; full companion reading incomplete. Evidence PASS does not certify proof or significance.',mutable_reference_exceptions=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],files=entries)
seal.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(dict(files=len(entries),seal=str(seal.relative_to(R)),sha256=hashlib.sha256(seal.read_bytes()).hexdigest(),nomination='HELD')))
