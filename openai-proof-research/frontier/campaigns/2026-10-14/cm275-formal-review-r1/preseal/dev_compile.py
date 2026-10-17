from pathlib import Path
import os,subprocess,sys
p=Path(__file__).resolve().parent
cache=p.parent/'formal/.lake/packages'
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(p)]+[str(q/'.lake/build/lib/lean') for q in cache.iterdir() if (q/'.lake/build/lib/lean').is_dir()])
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',*sys.argv[1:]],cwd=p,env=env,capture_output=True,text=True)
(p/'compile-checkpoint.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr);print('EXIT',r.returncode)
sys.exit(r.returncode)
