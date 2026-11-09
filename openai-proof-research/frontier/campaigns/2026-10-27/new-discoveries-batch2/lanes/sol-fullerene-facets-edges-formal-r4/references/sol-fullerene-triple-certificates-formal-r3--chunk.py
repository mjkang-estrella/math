from pathlib import Path
import sys,subprocess,json
L=Path(__file__).resolve().parent
C=json.loads((L/'coverage.json').read_text())
tag=sys.argv[1];start=int(sys.argv[2]);end=int(sys.argv[3])
for m in C[tag]['modules'][start:end]:
 r=subprocess.run([sys.executable,str(L/'runner.py'),'-o',m+'.olean',m+'.lean'],cwd=L,capture_output=True,text=True)
 if r.returncode:print(r.stdout,r.stderr);sys.exit(r.returncode)
print('PASS',tag,start,end)
