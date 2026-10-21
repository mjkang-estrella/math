#!/usr/bin/env python3
"""Seal only this review root, once. Run after all payload writing is finished."""
from pathlib import Path
from datetime import datetime,timezone
import json,runpy
ROOT=Path(__file__).resolve().parents[1]
assert ROOT.name=='structural-r161-proof-r1'
assert not (ROOT/'MANIFEST.json').exists(),'Already sealed; do not reseal.'
assert (ROOT/'FINAL.md').is_file() and (ROOT/'REPORT.md').is_file()
v=runpy.run_path(str(ROOT/'tools/verify.py'))
manifest={'schema':v['SCHEMA'],'sealed_at_utc':datetime.now(timezone.utc).isoformat(),'scope':'Exact own selected payload, with root FINAL.md/MANIFEST.json/REPORT.md outside; original rights retained for private derivatives. No mathematical gate.',**v['inventory'](ROOT)}
with (ROOT/'MANIFEST.json').open('x') as f:f.write(json.dumps(manifest,indent=2)+'\n')
print('SEALED ONCE:',len(manifest['files']),'payload files;',len(manifest['directories']),'directories.')
