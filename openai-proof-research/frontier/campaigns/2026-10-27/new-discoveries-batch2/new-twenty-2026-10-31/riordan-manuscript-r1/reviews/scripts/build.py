import pathlib,os,subprocess,sys,json
D=pathlib.Path(__file__).resolve().parents[1]; R=D/'extracted'; base=pathlib.Path('/home/mj-kang/Documents/Dev/math'); packages=base/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'; bins=base/'dlp-research/.tools/lean-4.34.1-linux/bin'
os.environ['LEAN_PATH']=':'.join([str(R)]+[str(p) for p in packages.glob('*/.lake/build/lib/lean')]);os.chdir(R)
mods=['Core']+[f'Row{i}' for i in range(15)]+['Table','Endpoint']
for m in mods:
 rc=subprocess.call([sys.executable,'-I',str(D/'scripts/run.py'),'build-'+m,str(bins/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',m+'.olean',m+'.lean'])
 if rc:sys.exit(rc)
for m in mods:
 rc=subprocess.call([sys.executable,'-I',str(D/'scripts/run.py'),'checker-'+m,str(bins/'leanchecker'),m])
 if rc:sys.exit(rc)
