import pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
jobs=[('signed-7-3','signed.py','7','3'),('signed-8-3','signed.py','8','3'),('signed-7-4','signed.py','7','4'),('hypertrees10','hypertrees.py','10'),('xray-cover-13','xray_cover.py','13'),('xray-cover-14','xray_cover.py','14')]
for name,sc,*args in jobs:
 print('START',name,flush=True)
 p=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),name,sys.executable,'-I',str(D/'scripts'/sc),*args])
 print('FINISHED',name,p.returncode,flush=True)
