from pathlib import Path
import shutil,subprocess,json,hashlib
b=Path(__file__).resolve().parent
r=b/'replay'
if r.exists():shutil.rmtree(r)
(r/'formal').mkdir(parents=True)
for p in (b/'formal').iterdir():
 if p.suffix=='.lean' or p.name=='run_lean.py':shutil.copyfile(p,r/'formal'/p.name)
shutil.copyfile(b/'verify.py',r/'verify.py')
assert not list((r/'formal').glob('*.olean'))
(r/'source-only-before.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (r/'formal').iterdir()},indent=2)+'\n')
raise SystemExit(subprocess.run(['python',str(r/'verify.py')],cwd=r).returncode)
