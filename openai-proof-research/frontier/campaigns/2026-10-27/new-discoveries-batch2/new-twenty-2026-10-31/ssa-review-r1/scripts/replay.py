import pathlib,subprocess,sys,os
D=pathlib.Path(__file__).resolve().parents[1]; B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/'
for m in ['Defs','Data','Checks','Bridge','Main','Endpoint','Audit']:
 for kind,args in [('build',[B+'lean','-j1','-DwarningAsError=true','-o',f'../build/SSA5/{m}.olean',f'SSA5/{m}.lean']),('check',[B+'leanchecker',f'SSA5.{m}'])]:
  p=subprocess.run([sys.executable,'-I',str(D/'scripts/run.py'),kind+'-'+m]+args)
  if p.returncode:sys.exit(p.returncode)
