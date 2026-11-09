import sys,json,re
from pathlib import Path
L=Path(sys.argv[1]); pat=re.compile(sys.argv[2],re.I)
for d in sorted(L.glob('sources/*-tree-*'))+sorted(L.glob('sources/pool-projects-*')):
    b=(d/'body').read_bytes()
    try:
        t=json.loads(b); paths=[x['path'] for x in t.get('tree',[])]; trunc=t.get('truncated')
    except Exception:
        paths=b.decode(errors='replace').split('\n'); trunc=None
    hits=[p for p in paths if pat.search(p)]
    print(d.name, 'entries',len(paths),'truncated',trunc,'hits',hits[:20])
