"""Read-only public payload verification. Original code MIT."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,sys
R=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser();p.add_argument('--manifest-sha256');args=p.parse_args()
    manifest=R/'public-manifest.json';data=manifest.read_bytes()
    if args.manifest_sha256 and hashlib.sha256(data).hexdigest()!=args.manifest_sha256:raise ValueError('external manifest hash mismatch')
    recs=json.loads(data)['files']; expected={'public-manifest.json'}
    for rec in recs:
        name=rec['path'];pp=PurePosixPath(name)
        if pp.is_absolute() or '..' in pp.parts or str(pp)!=name or name in expected:raise ValueError('invalid or duplicate member '+name)
        expected.add(name);path=R/name
        if path.is_symlink() or not path.is_file():raise ValueError('missing or linked file '+name)
        b=path.read_bytes()
        if len(b)!=rec['bytes'] or hashlib.sha256(b).hexdigest()!=rec['sha256']:raise ValueError('changed payload '+name)
    actual=set()
    for f in R.rglob('*'):
        if f.is_symlink():raise ValueError('unexpected symlink '+str(f.relative_to(R)))
        if f.is_file():actual.add(f.relative_to(R).as_posix())
    if actual!=expected:raise ValueError('membership mismatch; missing='+str(sorted(expected-actual))+' extra='+str(sorted(actual-expected)))
    # Required anchors prevent a hand-authored empty or reduced manifest from passing.
    required={'main.tex','formal-coverage.tex','output/pdf/main.pdf','formal-scope.json','README.md','RIGHTS.md','LICENSE-PROSE','LICENSE-CODE','checker-identities.json','support/inherited/author.py','support/inherited/reviewer.py','support/reviewer_portable.py','support/run_checks.py','support/verify_package.py','checks/finite-checks.json','checks/visual-review.json','source-identities.json','source-to-claim.md','metadata.json','formal/SeymourSupport.lean','formal/Controls.lean','formal/coverage.json','formal/lakefile.toml','formal/lake-manifest.json','formal/lean-toolchain','formal/output-manifest.json'}
    if not required<=expected:raise ValueError('required anchors missing: '+str(sorted(required-expected)))
    print(json.dumps({'status':'PASS_PUBLIC_INTEGRITY_ONLY','members':len(recs),'manifest_sha256':hashlib.sha256(data).hexdigest()}))
if __name__=='__main__':
    try:main()
    except Exception as exc:print('VERIFY FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
