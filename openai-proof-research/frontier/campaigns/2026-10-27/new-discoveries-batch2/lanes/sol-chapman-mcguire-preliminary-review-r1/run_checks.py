from pathlib import Path
import subprocess,shutil,json
L=Path(__file__).resolve().parent
if not (L/'checker-first-run.json').exists():shutil.copyfile(L/'checker-evidence.json',L/'checker-first-run.json')
if (L/'checker-run.log').exists() and not (L/'checker-failed-run.log').exists():shutil.copyfile(L/'checker-run.log',L/'checker-failed-run.log')
if (L/'checker-run.log').exists() and not (L/'checker-eq9-failed-run.log').exists():shutil.copyfile(L/'checker-run.log',L/'checker-eq9-failed-run.log')
p=subprocess.run(['python',str(L/'checker.py')],capture_output=True,text=True)
(L/'checker-run.log').write_text(p.stdout+p.stderr)
print(p.stdout+p.stderr);assert p.returncode==0
