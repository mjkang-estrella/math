#!/usr/bin/env python3
"""Read-only baseline check of only the 53 admitted author originals."""
from pathlib import Path
import hashlib,json,os,stat
ROOT=Path(__file__).resolve().parent
AUTHOR=ROOT.parent/'fresh-structural-discovery-r233'
def check():
    baseline=json.loads((ROOT/'author-baseline.json').read_bytes())
    assert baseline['author_root']=='frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r233'
    entries=baseline['files'];assert len(entries)==53
    for e in entries:
        p=AUTHOR/e['path'];s=p.lstat();assert stat.S_ISREG(s.st_mode)
        b=p.read_bytes()
        assert (len(b),format(stat.S_IMODE(s.st_mode),'04o'),hashlib.sha256(b).hexdigest())==(e['bytes'],e['mode'],e['sha256']),e['path']
    found=set();count=0
    for d,ds,fs in os.walk(AUTHOR,followlinks=False):
        for n in ds:assert stat.S_ISDIR((Path(d)/n).lstat().st_mode);count+=1
        for n in fs:found.add((Path(d)/n).relative_to(AUTHOR).as_posix())
    assert found=={e['path'] for e in entries};assert count==baseline['directories']==12
    return {'author_original_files':53,'subdirectories':12,'bytes_and_modes_unchanged':True,'exact_surface_unchanged':True,'read_only':True}
if __name__=='__main__':print(json.dumps(check(),sort_keys=True,indent=2))
