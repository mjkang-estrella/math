from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
for script in ['replay.py','negative.py','check-auditor.py']:
 rc=subprocess.run([sys.executable,'-I',str(r/'scripts'/script)],cwd=r).returncode
 if rc: raise SystemExit(rc)
print('PASS: strict rebuild, one-module kernel checks, full AuditR5, negative controls and auditor safety',flush=True)
