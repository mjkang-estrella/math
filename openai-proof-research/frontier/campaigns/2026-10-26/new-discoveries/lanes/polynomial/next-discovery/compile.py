from pathlib import Path
import os,subprocess,sys
base=Path(__file__).resolve().parent
pkgs=base.parents[5]/'2026-10-14/formal/.lake/packages'
# Resolve explicitly to keep the build independent of cwd.
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
build=base/'build'; src=base/'formal'/sys.argv[1]
env=dict(os.environ,LEAN_PATH=':'.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in pkgs.iterdir() if p.is_dir()]))
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-o',str(build/(src.stem+'.olean')),str(src)],env=env,capture_output=True,text=True)
print(r.stdout+r.stderr);sys.exit(r.returncode)
