from pathlib import Path
import hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bad=[];pairs=0
for n in ['original-copy-provenance.json','source-copy-provenance.json']:
    for row in json.loads((L/n).read_text()):
        pairs+=1
        for p in [Path(row['original']),L/row['copy']]:
            if not p.is_file() or sha(p)!=row['sha256']:bad.append(str(p))
freeze=json.loads((L/'scientific-freeze.json').read_text())
for path,h in freeze['files'].items():
    if sha(L/path)!=h:bad.append(path)
manifest=json.loads((L/'finalmanifest.json').read_text())
assert manifest['excludes']==['finalmanifest.json','verification-receipt.json']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
if actual!=set(manifest['files']):bad.append('manifest membership')
for path,h in manifest['files'].items():
    if sha(L/path)!=h:bad.append(path)
proc=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True)
if proc.returncode or proc.stdout!=(L/'checks.json').read_bytes():bad.append('checks exact replay')
guard=json.loads((L/'provenance.json').read_text())['guard']
if sha(Path(guard['path']))!=guard['sha256']:bad.append('external guard')
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),passed=not bad,original_copy_pairs=pairs,science_files=len(freeze['files']),manifest_files=len(manifest['files']),exact_check_replay=not proc.returncode and proc.stdout==(L/'checks.json').read_bytes(),bad=bad,excludes=manifest['excludes'],administrative_live_paths_bound=False)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));sys.exit(bool(bad))
