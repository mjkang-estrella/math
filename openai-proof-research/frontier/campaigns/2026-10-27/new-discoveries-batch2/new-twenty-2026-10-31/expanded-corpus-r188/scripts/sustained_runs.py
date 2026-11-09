import pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
for name,sc,args in [('signed-9-3','signed.py',['9','3']),('signed-8-4','signed.py',['8','4']),('hypertrees12','hypertrees.py',['12']),('xray-cover-15','xray_cover.py',['15'])]:
 print('START',name,flush=True)
 subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),name,sys.executable,'-I',str(D/'scripts'/sc),*args],check=True)
 print('FINISHED',name,flush=True)
