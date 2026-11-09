from pathlib import Path
import os,subprocess,sys
B=Path(__file__).resolve().parents[1]
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
L='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(B/'formal')]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if (x/'.lake/build/lib/lean').is_dir()]))
for mod in sys.argv[1:]:
 p=subprocess.run([L,'-DwarningAsError=true','-o',str(B/'formal'/f'{mod}.olean'),str(B/'formal'/f'{mod}.lean')],env=env,cwd=B/'formal',text=True,capture_output=True)
 (B/'verification'/f'{mod}.log').write_text(p.stdout+p.stderr)
 print(mod,p.returncode,flush=True);print(p.stdout+p.stderr,flush=True)
 if p.returncode:sys.exit(p.returncode)
