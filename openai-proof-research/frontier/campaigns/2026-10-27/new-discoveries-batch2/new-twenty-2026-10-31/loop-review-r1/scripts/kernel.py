import os,pathlib
D=pathlib.Path(__file__).resolve().parents[1];R=pathlib.Path('/home/mj-kang/Documents/Dev/math');B=R/'dlp-research/.tools/lean-4.34.1-linux/bin';P=R/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
os.environ.clear();os.environ.update(PATH=str(B)+':/usr/bin:/bin',LANG='C.UTF-8',LEAN_PATH=str(D/'extracted')+':'+':'.join(str(p) for p in P.glob('*/.lake/build/lib/lean')),LEAN_NUM_THREADS='1');os.chdir(D/'extracted');os.execv(str(B/'leanchecker'),[str(B/'leanchecker'),'Loop'])
