import pathlib,os,sys
D=pathlib.Path(__file__).resolve().parents[1];root=D.parents[6]
# Absolute pinned dependency paths, read only.
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir() if p.is_dir())+':'+str(pathlib.Path(os.environ.get('REPLAY_DIR',str(D/'lean'))))
os.chdir(pathlib.Path(os.environ.get('REPLAY_DIR',str(D/'lean'))))
os.execv('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',['lean','-j1','-M3500','-DwarningAsError=true',*sys.argv[1:]])
