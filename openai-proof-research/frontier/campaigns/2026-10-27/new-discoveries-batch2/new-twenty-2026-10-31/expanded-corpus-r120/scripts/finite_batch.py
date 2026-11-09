import subprocess,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
todo=[('egz', 'egz.py', [])]+[(f'delta-p{p}','delta.py',[str(p)]) for p in range(5,11)]+[(f'influence-{n}x{m}','influence.py',[str(n),str(m)]) for n,m in [(2,3),(2,5),(3,3),(3,5),(4,4),(4,5),(4,7),(4,8),(4,9),(4,10),(5,5),(5,6),(5,7),(6,6)]]
for name,script,args in todo:
 r=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),name,sys.executable,'-I',str(D/'scripts'/script),*args]);print(name,'wrapper rc',r.returncode,flush=True)
