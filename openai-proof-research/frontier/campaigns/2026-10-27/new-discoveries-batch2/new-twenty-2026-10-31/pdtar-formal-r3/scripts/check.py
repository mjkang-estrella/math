import os,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join([str(D)]+[str(x/'.lake/build/lib/lean') for x in P.iterdir() if x.is_dir()])
os.execv('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker',['leanchecker']+sys.argv[1:])
