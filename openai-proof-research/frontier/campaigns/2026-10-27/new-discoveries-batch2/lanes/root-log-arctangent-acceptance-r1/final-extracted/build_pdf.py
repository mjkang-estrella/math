from pathlib import Path
import os,subprocess,shutil,hashlib,json
P=Path(__file__).resolve().parent
T=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic')
(P/'build').mkdir(exist_ok=True)
cache=P/'build/cache/tectonic'
if not cache.exists():shutil.copytree('/home/mj-kang/.cache/tectonic',cache)
env=dict(os.environ,SOURCE_DATE_EPOCH='1793232000',XDG_CACHE_HOME=str(P/'build/cache'),XDG_CONFIG_HOME=str(P/'build/config'),XDG_DATA_HOME=str(P/'build/data'),TMPDIR=str(P/'build/tmp'))
for n in ['tmp','config','data']:(P/'build'/n).mkdir(exist_ok=True)
subprocess.run([str(T),'--only-cached','--untrusted','--keep-logs','--reruns','2','--outdir',str(P/'build'),'main.tex'],cwd=P,env=env,check=True,timeout=90)
log=(P/'build/main.log').read_text();assert 'Overfull' not in log
shutil.copy2(P/'build/main.pdf',P/'paper.pdf')
print(hashlib.sha256((P/'paper.pdf').read_bytes()).hexdigest())
