import pathlib,os,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];R=D/'extracted';base=pathlib.Path('/home/mj-kang/Documents/Dev/math');packages=base/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages';bins=base/'dlp-research/.tools/lean-4.34.1-linux/bin'
os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p) for p in packages.glob('*/.lake/build/lib/lean')]);os.environ['PATH']=str(bins)+':'+os.environ['PATH'];os.chdir(R)
for m in ['Core']+[f'Row{i}' for i in range(15)]+['Table','Endpoint']:
 rc=subprocess.call([sys.executable,'-I',str(D/'scripts/run.py'),'check-fixed-'+m,str(bins/'leanchecker'),m])
 if rc:sys.exit(rc)
rc=subprocess.call([sys.executable,'-I',str(D/'scripts/run.py'),'independent-audit',str(bins/'lean'),'-j1','-M3500','-DwarningAsError=true','IndependentAudit.lean']);sys.exit(rc)
