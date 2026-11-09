import os,pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir())+':'+str(D/'lean');os.environ['MALLOC_ARENA_MAX']='2'
r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j1','-M3500','-DwarningAsError=true','-o',str(D/'lean/Hurlbert.olean'),str(D/'lean/Hurlbert.lean')]);sys.exit(r.returncode)
