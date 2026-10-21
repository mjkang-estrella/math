#!/usr/bin/env python3
"""One-time own exact-byte payload seal; never reseals incoming author material."""
from pathlib import Path
import hashlib
import json
import os
import stat

ROOT=Path('frontier/campaigns/2026-10-14/t360s147-proof-r1')
ENVELOPES=['FINAL.md','MANIFEST.json','REPORT.md']
def main():
    if (ROOT/'MANIFEST.json').exists():
        raise ValueError('own seal already exists; refuse reseal')
    assert all((ROOT/n).is_file() for n in ['FINAL.md','REPORT.md'])
    files=[]
    for base,dirs,names in os.walk(ROOT,followlinks=False):
        for n in dirs:
            assert not (Path(base)/n).is_symlink()
        for n in names:
            p=Path(base)/n
            assert not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode)
            name=p.relative_to(ROOT).as_posix()
            if name in ENVELOPES: continue
            b=p.read_bytes()
            files.append({'path':name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    manifest={'schema':'exact-regular-byte-payload-v1','excluded_envelopes':ENVELOPES,'files':sorted(files,key=lambda r:r['path'])}
    (ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    anchors={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in ENVELOPES}
    print(json.dumps({'payload_files':len(files),'whole_root_files':len(files)+3,'detached_sha256':anchors,'mathematical_gate':False},indent=2))
if __name__=='__main__': main()
