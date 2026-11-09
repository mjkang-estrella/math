from pathlib import Path
import os,subprocess,hashlib,shutil,json
b=Path(__file__).resolve().parent
tex=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-25/bernstein-shape-lane/tools/tectonic')
env={**os.environ,'SOURCE_DATE_EPOCH':'1793232000','XDG_CACHE_HOME':str(b/'tex-cache')}
outputs=[]
for i in range(2):
 d=b/f'paper-build-{i}';d.mkdir(exist_ok=True)
 p=subprocess.run([str(tex),'--only-cached','--keep-logs','--outdir',str(d),str(b/'main.tex')],env=env,capture_output=True,text=True,timeout=60)
 (d/'build.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
 log=(d/'main.log').read_text();assert not any(x in log for x in ['Overfull','Underfull']),log
 outputs.append((d/'main.pdf').read_bytes())
assert outputs[0]==outputs[1],'PDF rebuild mismatch'
(b/'paper.pdf').write_bytes(outputs[0]);print(hashlib.sha256(outputs[0]).hexdigest())
