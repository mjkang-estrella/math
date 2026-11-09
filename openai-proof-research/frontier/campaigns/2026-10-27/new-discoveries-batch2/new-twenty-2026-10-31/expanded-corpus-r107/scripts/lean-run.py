import os,pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join([str(D/'lean')]+[str(p/'.lake/build/lib/lean') for p in P.iterdir()])
bin='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
r=subprocess.run([bin+'lean','-j1','-DwarningAsError=true',str(D/'lean/Digits.lean'),'-o',str(D/'lean/Digits.olean')]);sys.exit(r.returncode)
