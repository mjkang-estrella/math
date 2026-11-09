import os,pathlib,sys
root=pathlib.Path('/home/mj-kang/Documents/Dev/math'); d=pathlib.Path('replay/packet').resolve();pkgs=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
os.environ['PATH']=str(root/'dlp-research/.tools/lean-4.34.1-linux/bin')+':'+os.environ.get('PATH','');os.environ['LEAN_PATH']=str(d)+':'+':'.join(str(p) for p in pkgs.glob('*/.lake/build/lib/lean'));os.chdir(d)
b=root/'dlp-research/.tools/lean-4.34.1-linux/bin'/sys.argv[1]
a=[str(b)]+(['-j1','-DwarningAsError=true'] if sys.argv[1]=='lean' else [])+sys.argv[2:];os.execv(str(b),a)
