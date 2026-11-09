from pathlib import Path
import os,subprocess,sys
B=Path(__file__).resolve().parents[1]
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
L='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(B/'formal')]+[str(x/'.lake/build/lib/lean') for x in P.iterdir() if (x/'.lake/build/lib/lean').is_dir()]))
mod=sys.argv[1] if len(sys.argv)>1 else 'PolarFrameBridge'
p=subprocess.run([L,'-DwarningAsError=true','-o',str(B/'formal'/f'{mod}.olean'),str(B/'formal'/f'{mod}.lean')],cwd=B/'formal',env=env,text=True,capture_output=True)
(B/'logs'/f'{mod}.log').write_text(p.stdout+p.stderr)
print(p.stdout+p.stderr);sys.exit(p.returncode)
