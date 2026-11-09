from pathlib import Path
import sys,re
D=Path(__file__).resolve().parents[1]
p=D/'sources'/sys.argv[1];s=p.read_text()
for m in re.finditer(sys.argv[2],s,re.I):print('\nOFFSET',m.start(),s[max(0,m.start()-350):m.end()+1700])
