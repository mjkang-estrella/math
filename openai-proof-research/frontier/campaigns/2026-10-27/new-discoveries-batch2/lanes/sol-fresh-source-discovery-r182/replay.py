import subprocess,sys,json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
p=subprocess.run([sys.executable,str(L/'checks.py'),str(L/'checks-replay.json')],capture_output=True,text=True)
(L/'checks-replay.stdout.txt').write_text(p.stdout);(L/'checks-replay.stderr.txt').write_text(p.stderr)
assert p.returncode==0
assert (L/'checks-replay.json').read_bytes()==(L/'checks.json').read_bytes()
print('PASS: bounded exact replay byte-identical; not a universal theorem')
