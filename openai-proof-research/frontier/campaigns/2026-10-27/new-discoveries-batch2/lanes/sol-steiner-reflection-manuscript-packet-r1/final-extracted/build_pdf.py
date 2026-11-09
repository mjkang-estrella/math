"""Offline deterministic manuscript build, with bounded helper and TeX process."""
import os,resource,signal,subprocess,hashlib,json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
signal.alarm(230)
R=Path(__file__).resolve().parent
p=json.loads((R/'authoring-pins.json').read_text())
tool=Path(p['tectonic']);assert hashlib.sha256(tool.read_bytes()).hexdigest()==p['tectonic_sha256']
env=os.environ.copy();env.update(SOURCE_DATE_EPOCH='1793232000',FORCE_SOURCE_DATE='1',TZ='UTC')
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','BLIS_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[k]='1'
r=subprocess.run([str(tool),'--only-cached','--untrusted','--keep-logs','paper.tex'],cwd=R,env=env,capture_output=True,text=True,timeout=220)
(R/'pdf-build.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
print(hashlib.sha256((R/'paper.pdf').read_bytes()).hexdigest())
