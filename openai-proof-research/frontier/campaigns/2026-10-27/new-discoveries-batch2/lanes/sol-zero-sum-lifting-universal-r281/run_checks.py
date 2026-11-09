from pathlib import Path
import subprocess,sys
L=Path(__file__).resolve().parent
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,timeout=200)
(L/'checks.stdout').write_text(p.stdout);(L/'checks.stderr').write_text(p.stderr)
print(p.stdout[:1400]);print('returncode',p.returncode);sys.exit(p.returncode)
