"""Explicit prepare/validate/seal stages. Never called by the read-only verifier.
The unique seal is created exclusively after successful preseal validation.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time,runpy,ast
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i121_physical_transfer_bound';E=ROOT/'frontier/experiments/i121_physical_transfer_bound'
REPORT='frontier/iterations/i121-physical-transfer-bound.md'
def rel(p):return str(p.relative_to(ROOT))
def save(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert not (S/'seal.json').exists(),'No repair or reseal permitted'
assert len(sys.argv)==2
if sys.argv[1]=='inventory':
 for p in E.glob('*.py'):ast.parse(p.read_text())
 save(E/'diagnostic-result.json',runpy.run_path(str(E/'diagnostics.py'))['check']())
 paths={rel(p) for b in [S,E] for p in b.rglob('*') if p.is_file()}
 paths|={REPORT,rel(S/'inventory.json'),rel(E/'validation.json')}
 save(S/'inventory.json',dict(owned_paths=sorted(paths),seal_path=rel(S/'seal.json'),allowed_live_ledger_drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],selective_pdf_replay_limit=2))
elif sys.argv[1]=='validate':
 start=time.monotonic();p=subprocess.run([sys.executable,'-B',str(E/'verify.py'),'--preseal'],cwd=ROOT,capture_output=True,text=True)
 result=dict(status='PASS' if p.returncode==0 else 'FAIL',exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,command=['python3','-B',rel(E/'verify.py'),'--preseal'],stdout=p.stdout,stderr=p.stderr)
 if p.returncode==0:save(E/'validation.json',result)
 else:
  f=json.loads((S/'failures.json').read_text());f['current'].append(dict(kind='preseal validation failure',result=result));save(S/'failures.json',f)
 print(json.dumps(result,indent=2));sys.exit(p.returncode)
elif sys.argv[1]=='seal':
 val=json.loads((E/'validation.json').read_text());assert val['status']=='PASS' and val['exit_code']==0
 inv=json.loads((S/'inventory.json').read_text());expected=set(inv['owned_paths'])
 actual={rel(p) for b in [S,E] for p in b.rglob('*') if p.is_file()}|{REPORT};assert actual==expected
 hs={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(expected)}
 with (S/'seal.json').open('x') as f:json.dump(dict(schema='I121 single final seal',sha256=hs,scope='Immutable identity, not proof certification'),f,indent=2);f.write('\n')
 print(json.dumps(dict(owned_artifacts=len(hs),seal_sha256=hashlib.sha256((S/'seal.json').read_bytes()).hexdigest())))
else:raise AssertionError('unknown stage')
