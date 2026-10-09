"""Reproduce the bounded search; never write into the shared corpus cache."""
from pathlib import Path
import hashlib, json, re

ROOT=Path(__file__).resolve().parents[3]
CACHE=ROOT/'frontier/sources/i14_spectral_width_novelty_r3'
OUT=ROOT/'frontier/sources/i22_combinatorial_discovery/corpus-search.json'
PATTERNS=['prophet','secretary','correspondence','tight.cut','entropy.*matching','matching.*entropy','shifted.matching']

if __name__=='__main__':
    files=json.loads((CACHE/'corpus-manifest.json').read_text())['files']
    results=[]
    for row in files:
        b=(CACHE/'corpus'/row['path']).read_bytes()
        assert hashlib.sha256(b).hexdigest()==row['sha256'],row['path']
        hits=[]
        for i,line in enumerate(b.decode(errors='replace').splitlines(),1):
            terms=[p for p in PATTERNS if re.search(p,line,re.I)]
            if terms:hits.append({'line':i,'terms':terms,'text':line})
        if hits:results.append({'path':row['path'],'sha256':row['sha256'],'hits':hits})
    OUT.write_text(json.dumps({'patterns':PATTERNS,'records':results,'searched_files':len(files)},indent=2))
    print(json.dumps({'verified_and_searched':len(files),'hit_files':len(results)}))
