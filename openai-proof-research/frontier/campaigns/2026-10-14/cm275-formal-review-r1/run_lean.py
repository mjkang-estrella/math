# Original review support code MIT; Myeongjin Kang, no affiliation.
from pathlib import Path
import os, subprocess, sys
root=Path(__file__).resolve().parent
cache=root.parent/'formal/.lake/packages'
compiler=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
env=os.environ.copy()
env['LEAN_PATH']=':'.join([str(root/'work')]+[str(p/'.lake/build/lib/lean') for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()])
label=sys.argv[1]
r=subprocess.run([str(compiler),*sys.argv[2:]],cwd=root/'work',env=env,text=True,capture_output=True)
(root/'logs'/f'{label}.stdout').write_text(r.stdout)
(root/'logs'/f'{label}.stderr').write_text(r.stderr)
(root/'logs'/f'{label}.exit').write_text(str(r.returncode)+'\n')
print(r.stdout+r.stderr)
print('CHILD_EXIT',r.returncode)
sys.exit(r.returncode)
