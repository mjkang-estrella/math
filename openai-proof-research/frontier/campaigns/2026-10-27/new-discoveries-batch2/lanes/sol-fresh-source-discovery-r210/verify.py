from pathlib import Path
import hashlib,json,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    m=json.loads((L/'finalmanifest.json').read_text())
    assert m['exclusions']==['finalmanifest.json','verification-receipt.json']
    files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
    assert files==set(m['files'])
    for n,h in m['files'].items():assert sha(L/n)==h,n
    sci=json.loads((L/'scientific-bindings.json').read_text())
    for r in sci:assert sha(r['original'])==sha(r['copy'])==r['sha256'],r
    refs=json.loads((L/'reference-bindings.json').read_text())
    for r in refs:assert sha(r['path'])==r['sha256'],r
    drift=[];hist=alias=0
    for fn in ['history.json','alias-refresh.json']:
        for r in json.loads((L/fn).read_text())['records']:
            assert not r.get('missing'),r
            assert sha(r['snapshot_reference'])==r['sha256'],r
            p=Path(r['original'])
            if not p.exists() or sha(p)!=r['sha256']:drift.append(r['original'])
            if fn=='history.json':hist+=1
            else:alias+=1
    for n in [111,112,113]:assert any(f'sol-fresh-source-discovery-r{n}/SUMMARY.md' in r['original'] for r in json.loads((L/'history.json').read_text())['records'])
    r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,timeout=200)
    assert r.returncode==0 and r.stdout==(L/'checks.json').read_text() and r.stderr==(L/'checks.stderr').read_text()
    return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'finalmanifest.json'),'manifest_files':len(files),'scientific_bindings_verified':len(sci),'external_snapshot_indexes_and_reports_verified':len(refs),'canonical_report_snapshots_verified':hist,'alias_snapshots_verified_separately':alias,'mutable_report_original_drift':drift,'checker_replay':'exact stdout/stderr match','exclusions':m['exclusions'],'limits':'No universal mathematics or public-prior clearance certified; sampled guard limits apply.'}
if __name__=='__main__':
    try:x=main()
    except Exception as e:
        x={'status':'FAIL','error':repr(e)};(L/'verification-receipt.json').write_text(json.dumps(x,indent=2)+'\n');raise
    (L/'verification-receipt.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
