from pathlib import Path
import hashlib,json,subprocess
lane=Path(__file__).resolve().parent.parent
active=max((lane/'logs').glob('*_terminal_manifest.log'))
receipt=lane/'receipt'/(active.stem+'.json')
excluded=['SHA256-MANIFEST.json',str(active.relative_to(lane)),str(receipt.relative_to(lane))]
files={}
for p in sorted(lane.rglob('*')):
    if p.is_file():
        assert not p.is_symlink()
        rel=str(p.relative_to(lane))
        if rel not in excluded:
            files[rel]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
payload={'scope':'Own lane actual partial state, not an accepted certificate',
 'terminal_self_exclusions':excluded,'count':len(files),'files':files}
subprocess.run(['python3','-I','-B',str(lane/'write_lane.py'),'SHA256-MANIFEST.json'],
 input=json.dumps(payload,indent=2)+'\n',text=True,check=True)
assert all(hashlib.sha256((lane/f).read_bytes()).hexdigest()==meta['sha256'] for f,meta in files.items())
print(json.dumps({'count':len(files),'mismatches':[],
 'terminal_self_exclusions':excluded,'manifest_sha256':hashlib.sha256((lane/'SHA256-MANIFEST.json').read_bytes()).hexdigest()}))
