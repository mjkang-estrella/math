import subprocess,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for name,script,args in [('arithmetical','arithmetical.py',[]),('paneitz','paneitz.py',[]),('dprime-24-3','dprime.py',['24','3']),('dprime-32-3','dprime.py',['32','3'])]:
 subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),name,sys.executable,'-I',str(D/'scripts'/script),*args],check=True)
