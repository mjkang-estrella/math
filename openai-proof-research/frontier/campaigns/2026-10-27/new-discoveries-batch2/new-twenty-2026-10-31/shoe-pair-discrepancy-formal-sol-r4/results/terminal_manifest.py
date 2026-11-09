from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,data):
    subprocess.run(['python3','-I','-B','write_lane.py',p],input=json.dumps(data,indent=2,sort_keys=True),text=True,check=True)
active=sorted(Path('logs').glob('*_terminal-manifest.log'))
assert len(active)==1
log=str(active[0]); receipt='receipt/'+active[0].stem+'.json'
excluded=['SHA256-MANIFEST.json',log,receipt]
completed=[]
for p in sorted(Path('receipt').glob('*.json')):
    d=json.loads(p.read_text()); assert d['group_members_left']==[]
    completed.append({'path':str(p),'sha256':h(p),'exit':d['exit'],'label':d['label']})
write('results/COMPLETED-RECEIPTS.json',completed)
files=sorted(str(p) for p in Path('.').rglob('*') if p.is_file() and not p.is_symlink())
write('results/INVENTORY.json',{'scope':'Exclusive lane only, including copied inputs/helpers/pins/plans/sources/oleans/logs/audits/report/renders/extracted build',
 'files':sorted(set(files+['results/INVENTORY.json','SHA256-MANIFEST.json',receipt])),
 'completed_receipts':len(completed),'terminal_receipt':receipt,'exact_manifest_exclusions':excluded})
assert json.loads(Path('frozen-after.json').read_text())['mismatches']==[]
manifest={str(p):h(p) for p in sorted(Path('.').rglob('*')) if p.is_file() and not p.is_symlink() and str(p) not in excluded}
write('SHA256-MANIFEST.json',{'algorithm':'SHA256','exact_terminal_noncircular_self_exclusions':excluded,'files':manifest})
assert all(h(Path(p))==sha for p,sha in manifest.items())
print('MANIFEST_VERIFIED',len(manifest),'EXACT_EXCLUSIONS',excluded)
print('COMPLETED_RECEIPTS',len(completed),'ALL_RECORDED_GROUPS_EMPTY')
