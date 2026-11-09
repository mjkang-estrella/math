import os,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1];root=pathlib.Path('/home/mj-kang/Documents/Dev/math');BIN=root/'dlp-research/.tools/lean-4.34.1-linux/bin';P=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages';F=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else D/'fresh-replay'
env={'PATH':str(BIN)+':/usr/bin:/bin','LANG':'C.UTF-8','LEAN_PATH':str(F)+':'+':'.join(str(p) for p in P.glob('*/.lake/build/lib/lean')),'LEAN_NUM_THREADS':'1','MALLOC_ARENA_MAX':'2'}
os.environ.clear();os.environ.update(env);os.chdir(F);os.execv(str(BIN/'leanchecker'),[str(BIN/'leanchecker'),'Eventown'])
