import fnmatch,json
from pathlib import Path
ROOT=Path(__file__).parent
G=json.loads((ROOT/'private/guards.json').read_text())
def rejected(path):
 p=Path(path).as_posix().casefold()
 return p==G['own_root'] or p.startswith(G['own_root']+'/') or any(s in p for s in G['substrings']) or any(fnmatch.fnmatchcase(p,w) for w in G['wildcards']+G['additional_derivative_patterns'])
