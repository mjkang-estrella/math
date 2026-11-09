from pathlib import Path
import hashlib,json,sys,datetime,subprocess
D=Path(__file__).parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def entry(p):return dict(path=str(p.relative_to(D)),size=p.stat().st_size,sha256=digest(p))
def frozen_check():
    rows=json.loads((D/'frozen-inputs.json').read_text())
    for r in rows:
        assert digest(Path(r['original']))==r['sha256'],r['original']
        assert digest(D/r['copy'])==r['sha256'],r['copy']
    new=[]
    for p in sorted((D/'retrieved').glob('*.frozen')):
        a=Path(str(p)[:-7]);assert digest(a)==digest(p),str(a);new.append(str(a.relative_to(D)))
    return len(rows),new
if sys.argv[1]=='build':
    n,new=frozen_check()
    r=subprocess.run(['sh',str(D/'run-checks.sh')],capture_output=True,text=True)
    (D/'capped-check.stdout').write_text(r.stdout);(D/'capped-check.stderr').write_text(r.stderr)
    assert r.returncode==0
    sources=[p for p in sorted((D/'frozen/sources').iterdir()) if p.is_file()]
    sources += [p for p in sorted((D/'retrieved').iterdir()) if p.is_file()]
    (D/'sourcehashes.json').write_text(json.dumps([entry(p) for p in sources],indent=2)+'\n')
    files=[entry(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']]
    (D/'manifest.json').write_text(json.dumps({'excludes':['manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
    print('manifest written',len(files),'files; separate verification required')
elif sys.argv[1]=='verify':
    j=json.loads((D/'manifest.json').read_text())
    for r in j['files']:assert entry(D/r['path'])==r,r['path']
    actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in j['excludes']}
    assert actual=={r['path'] for r in j['files']}
    n,new=frozen_check()
    receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest(D/'manifest.json'),files_verified=len(j['files']),candidate_original_copy_pairs_verified=n,new_retrieval_pairs_verified=new,all_pass=True,administrative_policy='snapshot only; no live comparison')
    (D/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
