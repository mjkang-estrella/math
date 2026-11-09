#!/usr/bin/env python3
import pathlib,hashlib,json,zipfile
ROOT=pathlib.Path(__file__).resolve().parent
files=sorted([p.relative_to(ROOT).as_posix() for p in (ROOT/'src').rglob('*.lean')]+['run_build.py','replay.py','pins.json','resource-plan.json','ENDPOINT.md','BRIDGE-MAP.md','RESIDUALS.md'])
manifest={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in files}
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(ROOT/'proof-source-only.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
    for name in files+['manifest.json']:
        i=zipfile.ZipInfo(name,date_time=(2026,11,1,0,0,0));i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED
        z.writestr(i,(ROOT/name).read_bytes())
(ROOT/'archive-sha256.json').write_text(json.dumps({'sha256':hashlib.sha256((ROOT/'proof-source-only.zip').read_bytes()).hexdigest(),'manifest_files':len(files),'archive_files':len(files)+1},indent=2)+'\n')
print((ROOT/'archive-sha256.json').read_text())
