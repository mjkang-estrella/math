import subprocess,sys,pathlib,json
base=pathlib.Path(__file__).resolve().parent
modules=['MeanSourceDefs','Stolarsky','Transfer','MeanAnalyticDefs','MeanDerivatives','GapAnalytic','Centered','GapMonotonicity']
for m in modules:
 r=subprocess.run([sys.executable,str(base/'compile.py'),'fresh-source-replay','-o',m+'.olean',m+'.lean'])
 if r.returncode: sys.exit(r.returncode)
r=subprocess.run([sys.executable,str(base/'compile.py'),'fresh-source-replay','AllAudits.lean'])
sys.exit(r.returncode)
