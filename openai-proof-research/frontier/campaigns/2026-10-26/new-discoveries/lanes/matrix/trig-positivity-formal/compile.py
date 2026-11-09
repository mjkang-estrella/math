from pathlib import Path
import os,subprocess,sys
b=Path(__file__).resolve().parent
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=dict(os.environ,LEAN_PATH=':'.join([str(b/'formal')]+[str(p/'.lake/build/lib/lean') for p in pk.iterdir() if p.is_dir()]))
mod=sys.argv[1] if len(sys.argv)>1 else 'SourceCoefficients'
p=subprocess.run([lean,'-DwarningAsError=true','-o',str(b/'formal'/(mod+'.olean')),str(b/'formal'/(mod+'.lean'))],env=env,text=True,capture_output=True)
print(p.stdout+p.stderr);sys.exit(p.returncode)
