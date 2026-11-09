from pathlib import Path
import subprocess,json,sys
r=Path(__file__).resolve().parent.parent
for m in ['GapRankInverse']:
 p=subprocess.run([str(r/'scripts/lean.sh'),'-o',str(r/f'build/{m}.olean'),m+'.lean'])
 if p.returncode:sys.exit(p.returncode)
subprocess.run([sys.executable,'-I',str(r/'scripts/audit_r4.py')],check=True)
for m in ['ClosureAuditRound4','AuditRound4']:
 p=subprocess.run([str(r/'scripts/lean.sh'),'-o',str(r/f'build/{m}.olean'),m+'.lean'])
 if p.returncode:sys.exit(p.returncode)
