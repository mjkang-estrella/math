import subprocess,json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parents[1];root=D.parents[3]
patterns=D/'scripts/history-patterns.txt'
r=subprocess.run(['rg','-n','-i','-w','-F','-f',str(patterns),str(root),'-g','*.md','-g','*results*.json','-g','*ledger*.json','-g','!**/vendor/**'],capture_output=True,text=True)
lines=[l for l in r.stdout.splitlines() if '/expanded-corpus-r87/' not in l]
(D/'outputs/history-word-matches.txt').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(root=str(root),returncode=r.returncode,matches=len(lines),sha256=hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest(),stderr=r.stderr)))
