import pathlib,os,sys,subprocess
L=pathlib.Path(__file__).resolve().parents[1];B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={**os.environ,'PATH':str(B)+':'+os.environ.get('PATH',''),'LEAN_PATH':str(L/'extracted')+':'+':'.join(str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()))}
cmd=[str(B/'leanchecker'),'Code'] if sys.argv[1]=='checker' else [str(B/'lean'),'-j1','-M3500','-DwarningAsError=true',*sys.argv[1:]]
print(cmd,flush=True);sys.exit(subprocess.call(cmd,cwd=L/'extracted',env=env))
