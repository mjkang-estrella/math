"""Separate final verification. Invoke only under the assigned helper guard.
Manifest excludes itself and verification-receipt.json explicitly.
This checks provenance/integrity, not a proof of the unresolved conjecture.
"""
from pathlib import Path
import hashlib,json,datetime,subprocess

D=Path(__file__).resolve().parent
EXCLUDED={'manifest.json','verification-receipt.json'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    manifest=json.loads((D/'manifest.json').read_text())
    assert set(manifest['excluded'])==EXCLUDED
    actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()
            and str(p.relative_to(D)) not in EXCLUDED}
    assert actual==set(manifest['files']),('inventory mismatch',actual^set(manifest['files']))
    for rel,h in manifest['files'].items(): assert sha(D/rel)==h,rel
    bindings=0
    for name in ['inputs-index.json','retrieved-freeze.json']:
        for row in json.loads((D/name).read_text()):
            assert sha(Path(row['original']))==row['sha256'],row['original']
            assert sha(D/row['copy'])==row['sha256'],row['copy']
            bindings+=1
    # Re-extract to stdout without writing/changing scientific originals/copies.
    extractions=0
    for p in (D/'frozen').glob('*.pdf'):
        text=D/'sources'/p.with_suffix('.txt').name
        r=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
        assert r.stdout==text.read_bytes(),str(p)
        extractions+=1
    assert json.loads((D/'check-results.json').read_text())['status']=='PASS'
    assert not (D/'PROOF.md').exists()
    # Administrative snapshots are included in the artifact manifest but deliberately
    # have no binding to live mutable ledger/NEXT. Do not inspect live versions here.
    result=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                manifest_sha256=sha(D/'manifest.json'),files=len(actual),
                original_copy_bindings=bindings,deterministic_pdf_extractions=extractions,
                excluded=sorted(EXCLUDED),
                limit='Integrity/source verification only; no full conjecture or novelty certification.')
    (D/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__=='__main__': main()
