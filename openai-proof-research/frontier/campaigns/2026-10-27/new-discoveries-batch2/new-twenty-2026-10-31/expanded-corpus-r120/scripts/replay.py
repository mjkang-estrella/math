import os,pathlib,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1];P=D/'fresh-packet'
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
K=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={**os.environ,'PATH':str(B)+':'+os.environ.get('PATH',''),'LEAN_PATH':str(P)+':'+':'.join(str(p/'.lake/build/lib/lean') for p in sorted(K.iterdir()))}
cmd={'build':[str(B/'lean'),'-j1','-M3500','-DwarningAsError=true','-o','Code.olean','Code.lean'], 'check':[str(B/'leanchecker'),'Code'], 'audit':[str(B/'lean'),'-j1','-M3500','-DwarningAsError=true','Audit.lean']}[sys.argv[1]]
print('COMMAND',cmd,flush=True);raise SystemExit(subprocess.call(cmd,cwd=P,env=env))
