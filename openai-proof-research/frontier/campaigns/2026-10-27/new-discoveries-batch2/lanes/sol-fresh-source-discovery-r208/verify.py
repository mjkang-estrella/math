from pathlib import Path
import hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    bindings=json.loads((L/'primary-freeze.json').read_text())
    bindings.append(json.loads((L/'guard-binding.json').read_text()))
    for x in bindings:
        assert sha(Path(x['original']))==sha(L/x['copy'])==x['sha256'],x
    run=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,check=True)
    assert not run.stderr
    assert json.loads(run.stdout)==json.loads((L/'checks.json').read_text())
    manifest=json.loads((L/'finalmanifest.json').read_text())
    assert set(manifest['excluded'])=={'finalmanifest.json','verification-receipt.json'}
    actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(manifest['excluded'])
    assert actual==set(manifest['files'])
    for n,h in manifest['files'].items():assert sha(L/n)==h,n
    history=json.loads((L/'history-refresh.json').read_text())['records']
    drift=[]
    for x in history:
        assert sha(Path(x['canonical_copy']))==x['sha256'],x['canonical_copy']
        p=Path(x['original'])
        if not p.exists() or sha(p)!=x['sha256']:drift.append(str(p))
    aliases=json.loads((L/'alias-refresh.json').read_text())['records']
    for x in aliases:
        assert sha(Path(x['canonical_copy']))==x['current_copy_sha256']==x['sha256']
        p=Path(x['reference_absolute'])
        if not p.exists() or sha(p)!=x['current_original_sha256']:drift.append(str(p))
    return dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_bindings=len(bindings),scientific_original_copy='PASS',checker_replay='PASS',manifest='PASS',manifest_files=len(actual),manifest_sha256=sha(L/'finalmanifest.json'),excluded=manifest['excluded'],history_references=len(history),alias_references=len(aliases),mutable_reference_drift=drift,status='PASS',resource_policy='Launched by prescribed external guard; caps unchanged')
if __name__=='__main__':
    r=main();(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
