import subprocess,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
mods=['Core']+[f'Row{i}' for i in range(15)]+['Table','Endpoint','InfiniteFamily','EndpointStrong']
if len(sys.argv)>1: mods=sys.argv[1:]
for m in mods:
 r=subprocess.call([sys.executable,'-I',str(D/'scripts/lean.py'),'-o',m+'.olean',m+'.lean'])
 if r:sys.exit(r)
