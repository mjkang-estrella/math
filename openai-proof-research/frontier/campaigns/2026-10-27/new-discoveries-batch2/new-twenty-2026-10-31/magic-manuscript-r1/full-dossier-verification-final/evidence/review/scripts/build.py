import pathlib,os,subprocess
r=pathlib.Path(__file__).resolve().parents[1];bin=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');pk=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['PATH']=str(bin)+':'+os.environ['PATH'];os.environ['LEAN_PATH']=':'.join(str(x/'.lake/build/lib/lean') for x in pk.iterdir() if (x/'.lake/build/lib/lean').is_dir())+':'+str(r/'extracted');os.chdir(r/'extracted')
for name,args in [('build',[str(bin/'lean'),'-j1','-DwarningAsError=true','-o','Magic.olean','Magic.lean']),('audit',[str(bin/'lean'),'-j1','-DwarningAsError=true','ReviewAudit.lean']),('leanchecker',[str(bin/'leanchecker'),'Magic'])]:
 subprocess.run(['python',str(r/'scripts/run.py'),name]+args,check=True)
