"""Preparation/finalization helper. Unique exclusive seal creation after successful preseal validation."""
from pathlib import Path
import json,hashlib,sys
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i130_spectral_harmonic_discovery';E=ROOT/'frontier/experiments/i130_spectral_harmonic_discovery'
REPORT='frontier/iterations/i130-spectral-harmonic-discovery.md'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def rel(p):return str(p.relative_to(ROOT))
def listing():
 paths=[]
 for base in [S,E]:
  for p in base.rglob('*'):
   assert not p.is_symlink()
   if p.is_file():paths.append(rel(p))
 return sorted(set(paths+[REPORT]))
seal=S/'seal.json';assert not seal.exists(),'One seal only; no reseal.'
if sys.argv[1:]==['inventory']:
 paths=sorted(set(listing()+[rel(S/'inventory.json'),rel(E/'validation.json')]))
 (S/'inventory.json').write_text(json.dumps(dict(owned_paths=paths,seal_path=rel(seal),allowed_live_ledger_drift=LEDGERS,selective_pdf_replay_limit=0),indent=2)+'\n')
 print(len(paths),'canonical globally sorted owned paths before seal')
elif sys.argv[1:]==['seal']:
 inv=json.loads((S/'inventory.json').read_text());assert listing()==inv['owned_paths']
 val=json.loads((E/'validation.json').read_text());assert val['status']=='PASS' and val['exit_code']==0 and val['result']['mode']=='preseal'
 hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inv['owned_paths']}
 with seal.open('x') as f:json.dump(dict(sha256=hashes,scope='Immutable evidence and exact inventory; not mathematical certification.'),f,indent=2);f.write('\n')
 print(hashlib.sha256(seal.read_bytes()).hexdigest())
else:raise SystemExit('Use inventory or seal; offline verifier never calls this helper.')
