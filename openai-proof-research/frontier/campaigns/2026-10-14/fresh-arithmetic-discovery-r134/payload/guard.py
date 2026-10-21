from pathlib import Path
import fnmatch,json,os,re
BASE=Path(__file__).resolve().parent
POLICY=json.loads((BASE/'private/policy.json').read_text())
def excluded(path):
    p=path.as_posix().casefold()
    return (any(fnmatch.fnmatchcase(p,w) for w in POLICY['wildcards']) or any(a in p for a in POLICY['substrings']) or bool(re.search(r'(?:^|/)(?:history[0-9][^/]*|further-history-[^/]*|[^/]*screen-[^/]*|[^/]*screen[0-9]+[^/]*)(?:/|$)',p)))
def eligible():
    for d,ds,fs in os.walk('.',followlinks=False):
        base=Path(d)
        ds[:]=sorted(x for x in ds if not excluded(base/x) and not (base/x).is_symlink())
        for f in sorted(fs):
            p=base/f
            if not excluded(p) and not p.is_symlink(): yield p
