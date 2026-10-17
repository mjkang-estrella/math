#!/usr/bin/env python3
"""Exercise the read-only verifier on disposable exact copies. MIT, Myeongjin Kang.
Run only in a working copy, since --output creates a new evidence file.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    root = Path(__file__).absolute().parent
    m = json.loads((root / 'manifest.json').read_text())
    anchor = hashlib.sha256((root / 'manifest.json').read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cases = []
    with tempfile.TemporaryDirectory(prefix='review-controls-', dir=args.output.parent) as td:
        for case in ['positive', 'wrong-anchor', 'changed-payload', 'missing-payload', 'extra-file', 'extra-empty-directory', 'symlink-payload']:
            p = Path(td) / case
            p.mkdir()
            for name in m['directories']:
                (p / name).mkdir(parents=True, exist_ok=True)
            for e in m['files']:
                shutil.copyfile(root / e['path'], p / e['path'])
            shutil.copyfile(root / 'manifest.json', p / 'manifest.json')
            use_anchor = anchor
            if case == 'wrong-anchor':
                use_anchor = '0' * 64
            elif case == 'changed-payload':
                with (p / 'review.md').open('ab') as f:
                    f.write(b'\nchanged\n')
            elif case == 'missing-payload':
                (p / 'review.md').unlink()
            elif case == 'extra-file':
                (p / 'extra.txt').write_text('extra')
            elif case == 'extra-empty-directory':
                (p / 'extra-empty').mkdir()
            elif case == 'symlink-payload':
                (p / 'review.md').unlink()
                (p / 'review.md').symlink_to(root / 'review.md')
            r = subprocess.run([sys.executable, '-B', str(p / 'verify_review.py'), '--anchor', use_anchor], capture_output=True, text=True)
            expected = r.returncode == 0 if case == 'positive' else r.returncode != 0
            if not expected or (case != 'positive' and 'REJECT:' not in r.stderr):
                raise SystemExit('unexpected control result: ' + case + repr(r))
            cases.append({'case':case,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'expected_result_observed':True})
    out = {'tested_manifest_sha256':anchor,'note':'Controls ran before inclusion of this receipt in the final detached seal; verifier code is unchanged. Final positive and wrong-anchor runs are reported externally.','verifier_sha256':hashlib.sha256((root/'verify_review.py').read_bytes()).hexdigest(),'cases':cases}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','cases':len(cases),'tested_manifest_sha256':anchor}))


if __name__ == '__main__':
    main()
