"""One-time local seal; refuses to replace any existing seal file."""
import json
from pathlib import Path
from verify import digest, inventory
r=Path(__file__).resolve().parents[1]
assert not (r/'MANIFEST.json').exists() and not (r/'FINAL.json').exists(), 'already sealed'
assert (r/'REPORT.md').is_file()
entries=[]
for name in inventory(r):
    data=(r/name).read_bytes(); entries.append({'path':name,'bytes':len(data),'sha256':digest(data)})
m={'schema':'r110-exact-payload-v1','excluded_root':'scratch/','outside_payload':['MANIFEST.json','FINAL.json','REPORT.md'],'files':entries}
with (r/'MANIFEST.json').open('x') as h: h.write(json.dumps(m,indent=2)+'\n')
f={'schema':'r110-final-v1','status':'PREFREEZE/no nominee','frozen_statement':None,'provenance':'Codex / GPT-6 Astra / high / default service tier','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source_operations':'stipulated true; not audited','manifest_sha256':digest((r/'MANIFEST.json').read_bytes()),'outside_report_sha256':digest((r/'REPORT.md').read_bytes()),'parent_authority':'integration, independent reviews and acceptance/count remain with parent','claim':'No complete full-scope result; supporting derivation and precise gaps retained.'}
with (r/'FINAL.json').open('x') as h: h.write(json.dumps(f,indent=2)+'\n')
for name in ['FINAL.json','MANIFEST.json','REPORT.md']: print(digest((r/name).read_bytes()),name)
