import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
lanes=p.parent
names=['root-log-arctangent-certificate-r2','root-log-arctangent-candidate-r1','root-log-arctangent-source-r3','sol-log-arctangent-derivative-review-r2','sol-log-arctangent-investment-review-r3','root-log-arctangent-formal-r1']
hashes={str(f.relative_to(lanes)):hashlib.sha256(f.read_bytes()).hexdigest() for name in names for f in sorted((lanes/name).rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
(p/'input-before.json').write_text(json.dumps(hashes,indent=2)+'\n')
