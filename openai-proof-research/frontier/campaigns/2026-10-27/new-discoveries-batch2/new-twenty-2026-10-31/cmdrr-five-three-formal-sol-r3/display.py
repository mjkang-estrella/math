import os,sys
from pathlib import Path
p=Path(sys.argv[1]); a=int(sys.argv[2]) if len(sys.argv)>2 else 0; b=int(sys.argv[3]) if len(sys.argv)>3 else 16000
s=p.read_text(); t=f'FILE {p} chars {a}:{min(b,len(s))}/{len(s)}\n'+s[a:b]
print(t)
with open(f'/proc/{os.getppid()}/fd/1','w') as out: out.write(t)
