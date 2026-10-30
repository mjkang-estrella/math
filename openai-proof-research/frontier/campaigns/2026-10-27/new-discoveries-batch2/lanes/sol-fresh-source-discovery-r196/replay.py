from pathlib import Path
import subprocess,sys,hashlib
L=Path(__file__).resolve().parent
for script,out in [('checks.py','checks.json'),('correlation-checks.py','correlation-checks.json')]:
 before=(L/out).read_bytes() if (L/out).exists() else None
 subprocess.run([sys.executable,str(L/script)],check=True)
 if before is not None:assert before==(L/out).read_bytes(),out
print('Exact diagnostic replay PASS. This is not a full proof verifier.')
