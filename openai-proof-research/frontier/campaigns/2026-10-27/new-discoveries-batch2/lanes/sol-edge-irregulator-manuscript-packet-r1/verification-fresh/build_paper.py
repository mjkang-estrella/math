from pathlib import Path
import hashlib,json,os,shutil,subprocess
P=Path(__file__).resolve().parent
T=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in json.loads((P/'paper-pins.json').read_text()).items():assert sha(Path(f))==h,f
for d in ['paper-build','paper-cache','paper-tmp']:(P/d).mkdir(exist_ok=True)
if not (P/'paper-cache/tectonic').exists():shutil.copytree(Path.home()/'.cache/tectonic',P/'paper-cache/tectonic')
env=dict(os.environ);env.update(TMPDIR=str(P/'paper-tmp'),XDG_CACHE_HOME=str(P/'paper-cache'),SOURCE_DATE_EPOCH='1793232000',TZ='UTC')
cmd=[str(T),'--only-cached','--keep-logs','--outdir',str(P/'paper-build'),str(P/'paper.tex')]
r=subprocess.run(cmd,cwd=P,env=env,capture_output=True,text=True)
(P/'paper-build/stdout.log').write_text(r.stdout);(P/'paper-build/stderr.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
log=(P/'paper-build/paper.log').read_text();assert 'Overfull' not in log
shutil.copyfile(P/'paper-build/paper.pdf',P/'paper.pdf')
print('paper sha256',sha(P/'paper.pdf'))
