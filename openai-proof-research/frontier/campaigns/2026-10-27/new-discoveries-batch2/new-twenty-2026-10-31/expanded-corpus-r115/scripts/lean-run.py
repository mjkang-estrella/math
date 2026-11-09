import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];P=D.parents[3]/'2026-10-14/formal/.lake/packages'
# Resolve explicitly, keeping dependencies read-only.
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir() if p.is_dir())+':'+str(D/'lean')
os.execv('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'+sys.argv[1],sys.argv[1:])
