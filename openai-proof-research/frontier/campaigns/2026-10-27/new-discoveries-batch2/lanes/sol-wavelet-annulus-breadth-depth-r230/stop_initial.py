import os,signal,json
from pathlib import Path
rows=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().split(b'\0')
  if args and b'python' in args[0] and len(args)>1 and args[1].endswith(b'/coding.py'):
   os.kill(int(p.name),signal.SIGTERM);rows.append(int(p.name))
 except (OSError,ProcessLookupError):pass
L=Path(__file__).resolve().parent
(L/'initial-coding-failure.json').write_text(json.dumps({'stopped_pids':rows,'reason':'Initial quadratic interval intersection and Gauss-Seidel variant superseded by linear sorted intersection with simultaneous preimages. Initial run produced no scientific result; manually terminated, no resource cap raised.'},indent=2))
print(rows)
