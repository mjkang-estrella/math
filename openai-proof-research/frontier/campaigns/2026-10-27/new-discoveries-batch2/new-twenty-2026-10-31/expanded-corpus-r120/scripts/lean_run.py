import os,pathlib,subprocess,sys
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir())
cmd=['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-j1','-M3500','-DwarningAsError=true',*sys.argv[1:]]
raise SystemExit(subprocess.call(cmd))
