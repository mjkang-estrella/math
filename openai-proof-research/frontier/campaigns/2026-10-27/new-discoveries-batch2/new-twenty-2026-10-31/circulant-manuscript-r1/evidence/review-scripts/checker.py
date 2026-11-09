import pathlib,os,subprocess
W=pathlib.Path(__file__).resolve().parents[1];R=W/'extracted'
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');B=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
os.environ['PATH']=str(B)+':'+os.environ['PATH'];os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p/'.lake/build/lib/lean') for p in P.iterdir()]);os.environ['LEAN_NUM_THREADS']='1'
for n in ['Circulant','Bridge','Endpoint','Audit']:
 subprocess.run(['python3','-I',str(W/'scripts/limited.py'),'checker-'+n,str(B/'leanchecker'),'-v',n],cwd=R)
