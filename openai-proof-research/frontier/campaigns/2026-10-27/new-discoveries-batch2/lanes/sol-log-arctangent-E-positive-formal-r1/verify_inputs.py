import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
before=json.loads((p/'input-before.json').read_text())
after={n:sha(p.parent/n) for n in before}
(p/'input-after.json').write_text(json.dumps(after,indent=2)+'\n')
freeze=json.loads((p.parent/'root-log-arctangent-certificate-r2/review-freeze.json').read_text())['hashes']
checks={n:sha(p.parent/'root-log-arctangent-certificate-r2'/n)==h for n,h in freeze.items()}
changed=[n for n,h in before.items() if after[n]!=h]
result={'all_inputs_unchanged':not changed,'changed':changed,'six_frozen_hashes':checks,'binary_sha256':sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')),'runner_byte_identical':(p/'formal/run_lean.py').read_bytes()==(p.parent/'root-cascade-formal-r1/formal/run_lean.py').read_bytes()}
(p/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
assert not changed and all(checks.values()) and result['runner_byte_identical']
assert result['binary_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
