import subprocess,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in [3,5,7,11,13,17,19,23,29,31]:
 for n in ([3,4,5,6,7,8] if p<=19 else [8]):
  subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),f'primitive-{p}-{n}',sys.executable,'-I',str(D/'scripts/primitive.py'),str(p),str(n)],check=True)
for p,n in [(3,7),(3,8),(3,9),(5,11),(5,12),(7,15)]:
 subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),f'primitive-{p}-{n}',sys.executable,'-I',str(D/'scripts/primitive.py'),str(p),str(n)],check=True)
