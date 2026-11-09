"""Fresh local source-only strict replay; serial Lean and exhaustive declaration audits."""
import hashlib, json, os, pathlib, re, resource, shutil, subprocess, sys, time
import signal
signal.alarm(50)
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (45,45))
base=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
env=dict(os.environ, OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
os.environ.update(env)
# This bounded diagnostic only prepares source files. Invoke compile.py separately.
names=[]
modules=['MeanSourceDefs','Stolarsky','Transfer']
for module in modules:
    text=(base/'formal'/f'{module}.lean').read_text()
    found=re.findall(r'^\s*(?:noncomputable\s+)?(?:def|theorem)\s+(\w+)',text,re.M)
    names.extend(found)
checks='import Transfer\nset_option autoImplicit false\nset_option warningAsError true\n'
for name in names:
    checks+=f'#check @LogArctangentSource.{name}\n#print axioms LogArctangentSource.{name}\n'
(base/'formal'/'Checks.lean').write_text(checks)
fresh=base/'fresh-source-replay'
if fresh.exists():
    raise SystemExit('Refusing to overwrite existing replay directory')
fresh.mkdir()
for name in [f'{m}.lean' for m in modules]+['Checks.lean','run_lean.py']:
    shutil.copyfile(base/'formal'/name,fresh/name)
(base/'declarations.json').write_text(json.dumps(names,indent=2)+'\n')
print(json.dumps({'source_files':sorted(p.name for p in fresh.iterdir()),'declarations':len(names),'diagnostic_limits':{'AS':512*1024**2,'CPU':45},'elapsed':time.monotonic()-start}))
