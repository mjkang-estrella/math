from pathlib import Path
import os,subprocess
r=Path(__file__).parent.resolve()
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,LEAN_PATH=':'.join(str(d/'.lake/build/lib/lean') for d in p.iterdir() if d.is_dir()))
t=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-DwarningAsError=true','-o',str(r/'build/TaxicabGeometry.olean'),str(r/'formal/TaxicabGeometry.lean')],env=env,text=True,capture_output=True)
(r/'build/TaxicabGeometry.log').write_text(t.stdout+t.stderr)
print(t.stdout+t.stderr)
raise SystemExit(t.returncode)
