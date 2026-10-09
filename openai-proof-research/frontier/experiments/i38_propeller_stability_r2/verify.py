#!/usr/bin/env python3
"""Offline verification; never reseals, fetches, or writes author files."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];E=Path(__file__).resolve().parent
S=ROOT/'frontier/sources/i38_propeller_stability_r2'
def load(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    seal=load(S/'artifact-seal.json')
    for r in seal['files']:
        p=ROOT/r['path'];assert len(p.read_bytes())==r['bytes'] and sha(p)==r['sha256'],r['path']
    drift=[]
    for r in load(S/'input-manifest.json'):
        assert sha(ROOT/r['frozen'])==r['sha256'],r['frozen']
        if sha(ROOT/r['path'])!=r['sha256']:
            assert r['mutable'],'IMMUTABLE dependency drift: '+r['path']
            drift.append(r['path'])
    for r in load(S/'author-before.json'):assert sha(ROOT/r['path'])==r['sha256'],'Author drift: '+r['path']
    for r in load(S/'read-passages.json'):
        p=ROOT/r['path'];assert sha(p)==r['file_sha256'],r['path']
        lines=p.read_bytes().splitlines(keepends=True)
        for span in r['lines']:
            data=b''.join(lines[span['start_line']-1:span['end_line']])
            assert hashlib.sha256(data).hexdigest()==span['sha256'],r['path']
    for r in load(S/'literature/manifest.json'):
        p=S/'literature'/r['name'];assert sha(p)==r['sha256'] and len(p.read_bytes())==r['bytes']
        assert r['status']==200 and r['equal_to_author_response']
        assert p.read_bytes()==(ROOT/'frontier/sources/i38_inequality_stability_discovery/literature'/r['name']).read_bytes()
    for r in load(S/'selected-pinned-manifest.json'):
        p=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'/r['path'];data=p.read_bytes()
        assert sha(p)==r['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob']
    from review_audit import run as audit
    coverage=audit();assert coverage==load(S/'corpus-audit.json')
    diagnostic=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],cwd=ROOT,capture_output=True,text=True,check=True)
    checks=json.loads(diagnostic.stdout);assert checks==load(E/'diagnostics-record.json')
    from reproduce_author import run as reproduce
    author=reproduce()
    result={'status':'PASS','sealed_files':len(seal['files']),'fresh_primary_responses':7,'selected_source_files':11,'read_passage_files':len(load(S/'read-passages.json')),'corpus_files':coverage['files'],'corpus_bytes':coverage['bytes'],'tree_entries':coverage['tree_entries'],'manuscripts':coverage['manuscripts'],'independent_exact_margins':len(checks['exact']['rational_interval_certificates']),'unchanged_author_files':author['unchanged_author_files'],'author_evidence_status':author['author_verification']['status'],'mutable_live_ledger_drift_since_review_snapshot':drift,'author_verification':author['author_verification'],'immutable_dependency_drift':[],'limitation':'Offline integrity/diagnostic PASS; mathematical proof decision is recorded in the sealed review. Noncertified floating checks are not proof.'}
    (E/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='author_verification'},indent=2))
    return 0
if __name__=='__main__':raise SystemExit(main())
