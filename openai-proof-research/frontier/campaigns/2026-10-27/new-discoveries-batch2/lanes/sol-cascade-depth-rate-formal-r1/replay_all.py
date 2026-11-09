import pathlib,subprocess,sys,shutil,json
b=pathlib.Path(__file__).resolve().parent
r=b/'replay'
# Delete all generated replay artifacts before copying ONLY source and byte-identical runner.
if r.exists():shutil.rmtree(r)
r.mkdir()
for p in (b/'formal').iterdir():
 if p.suffix=='.lean' or p.name=='run_lean.py':shutil.copyfile(p,r/p.name)
assert not list(r.glob('*.olean'))
for m in ['DepthDefs','DepthArithmetic','DepthAnalysis','Checks']:
 args=[sys.executable,str(b/'audit.py'),'replay']
 if m!='Checks':args+=['-o',m+'.olean']
 args+=[m+'.lean']
 subprocess.run(args,check=True)
print('Fresh source-only serial replay PASS')
