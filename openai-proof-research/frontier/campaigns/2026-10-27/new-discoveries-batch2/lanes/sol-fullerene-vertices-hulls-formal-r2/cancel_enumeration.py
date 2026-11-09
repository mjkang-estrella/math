from pathlib import Path
import os,signal
for p in Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   args=(p/'cmdline').read_bytes().split(b'\0')
   if args and args[0].endswith(b'/lean') and b'RationalEnumeration.lean' in args:
    os.killpg(int(p.name),signal.SIGKILL);print('cancelled experimental enumeration',p.name)
  except (FileNotFoundError,PermissionError,ProcessLookupError):pass
