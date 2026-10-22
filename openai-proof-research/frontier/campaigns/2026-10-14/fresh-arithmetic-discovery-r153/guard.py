from pathlib import Path
import json,fnmatch,os,re
ROOT=Path.cwd();OWN=Path(__file__).parent
G=json.loads((OWN/'private/guards.json').read_text())
def excluded(p):
 s=p.as_posix().casefold()
 return any(fnmatch.fnmatchcase(s,x) for x in G['wildcards']) or any(x in s for x in G['substrings']) or any(fnmatch.fnmatchcase(c,x) for c in s.split('/') for x in G['extra_component_patterns'])
def eligible():
 for base,dirs,files in os.walk('.',followlinks=False):
  d=Path(base)
  dirs[:]=sorted(x for x in dirs if not excluded(d/x) and not (d/x).is_symlink())
  for n in sorted(files):
   p=d/n
   if excluded(p) or p.is_symlink():continue
   if not any(x in p.parts for x in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']):continue
   yield p
