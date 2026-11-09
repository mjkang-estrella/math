from pathlib import Path
import subprocess,sys
L=Path(__file__).resolve().parent
for m in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(L/'runner.py'),'-o',m+'.olean',m+'.lean'],cwd=L)
 if r.returncode:sys.exit(r.returncode)
