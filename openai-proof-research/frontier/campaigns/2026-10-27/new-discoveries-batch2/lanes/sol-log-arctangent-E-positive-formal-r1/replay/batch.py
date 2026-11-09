from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for f in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(p/'run.py'),f])
 if r.returncode:sys.exit(r.returncode)
