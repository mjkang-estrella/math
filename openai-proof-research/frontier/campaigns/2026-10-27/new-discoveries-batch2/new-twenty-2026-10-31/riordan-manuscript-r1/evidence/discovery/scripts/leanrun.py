import pathlib,os,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');F=D/os.environ.get('LANE_BUILD','formal')
assert F.resolve().is_relative_to(D)
os.environ['LEAN_PATH']=str(F)+':'+':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir() if p.is_dir())
os.environ['PATH']=str(B)+':'+os.environ['PATH'];os.environ['LEAN_NUM_THREADS']='2'
args=sys.argv[1:]
cmd=[str(B/'lean'),'-j2','-M3500','-DwarningAsError=true',*args]
if args[0]=='--checker':cmd=[str(B/'leanchecker'),*args[1:]]
raise SystemExit(subprocess.run(cmd,cwd=F).returncode)
