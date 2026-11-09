import os,pathlib,subprocess,sys
W=pathlib.Path(__file__).resolve().parent;P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
os.environ['LEAN_PATH']=':'.join([str(W/'fresh')]+[str(p/'.lake/build/lib/lean') for p in P.iterdir()])
cmd=([B+'leanchecker','Digits','Audit'] if sys.argv[1]=='check' else [B+'lean','-j1','-DwarningAsError=true','fresh/'+sys.argv[1]+'.lean','-o','fresh/'+sys.argv[1]+'.olean'])
os.environ['PATH']=B+':'+os.environ['PATH'];os.chdir(W);os.execv(cmd[0],cmd)
