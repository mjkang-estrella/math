"""One-time artifact freeze. Never refresh an existing seal."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i39_quantum_spectral_discovery';E=Path(__file__).parent
seal=S/'artifact-seal.json'
assert not seal.exists(), 'Existing seal must never be refreshed'
paths=sorted([R/'frontier/iterations/i39-quantum-spectral-discovery.md']+[p for d in [S,E] for p in d.rglob('*') if p.is_file()])
files={str(p.relative_to(R)):{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths}
with seal.open('x') as f:json.dump({'format':'I39 SHA-256 artifact freeze v1','note':'Includes all owned artifacts except this seal. Immutable reused dependencies are separately bound through frozen inputs. Do not refresh.','files':files},f,indent=2);f.write('\n')
print(json.dumps({'sealed_files':len(files),'seal_sha256':hashlib.sha256(seal.read_bytes()).hexdigest()}))
