from pathlib import Path
import os,subprocess,sys
root=Path(__file__).resolve().parent
packages=root.parent.parent/'2026-10-14/formal/.lake/packages'
env=dict(os.environ,LEAN_PATH=':'.join(str(p/'.lake/build/lib/lean') for p in packages.iterdir() if p.is_dir()))
p=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',str(root/'formal'/('BernsteinShape.lean' if len(sys.argv)==1 else sys.argv[1]))],env=env,text=True,capture_output=True)
print(p.stdout+p.stderr,end='');sys.exit(p.returncode)
