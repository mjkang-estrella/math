from pathlib import Path
import os,json,hashlib,subprocess
p=Path(__file__).resolve().parent
log=Path(os.readlink('/proc/self/fd/1')).resolve()
assert log.parent==p/'logs'
receipt=p/'receipt'/(log.stem+'.json')
excluded=['SHA256-MANIFEST.json',str(log.relative_to(p)),str(receipt.relative_to(p))]
files={str(q.relative_to(p)):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(p.rglob('*')) if q.is_file() and str(q.relative_to(p)) not in excluded}
for q in (p/'receipt').glob('*.json'):
 r=json.loads(q.read_text()); assert r.get('group_members_left',[])==[],str(q)
frozen=json.loads((p/'frozen-after.json').read_text()); assert not frozen['mismatches']
obj=dict(files=files,terminal_self_exclusions=excluded,scope='Every actual lane file except exactly manifest and its current runner log/receipt; no filename-pattern exclusion.',frozen_after=frozen,credit=0,campaign='55/60 beyond39prior')
subprocess.run(['python3','-I','-B',str(p/'write_lane.py'),'SHA256-MANIFEST.json'],input=json.dumps(obj,indent=2),text=True,check=True)
print('TERMINAL_MANIFEST_FILES',len(files),'EXACT_EXCLUSIONS',json.dumps(excluded),'FROZEN_MISMATCHES',len(frozen['mismatches']))
