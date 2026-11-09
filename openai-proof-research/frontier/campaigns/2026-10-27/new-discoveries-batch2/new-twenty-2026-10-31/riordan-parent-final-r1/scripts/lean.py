import pathlib,os,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
B=pathlib.Path('/home/mj-kang/Documents/Dev/math')
P=B/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
BIN=B/'dlp-research/.tools/lean-4.34.1-linux/bin'
R=pathlib.Path(os.environ.get('REPLAY_ROOT',str(D/'formal')))
os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p) for p in P.glob('*/.lake/build/lib/lean')])
os.environ['PATH']=str(BIN)+':'+os.environ['PATH']
os.chdir(R)
args=sys.argv[1:]
if args[0]=='check': cmd=[str(BIN/'leanchecker'),args[1]]
else: cmd=[str(BIN/'lean'),'-j1','-M3500','-DwarningAsError=true',*args]
sys.exit(subprocess.call([sys.executable,'-I',str(D/'scripts/run.py'),'lean-'+pathlib.Path(args[-1]).stem,*cmd]))
