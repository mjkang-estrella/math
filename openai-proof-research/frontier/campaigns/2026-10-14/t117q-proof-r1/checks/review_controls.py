#!/usr/bin/env python3
"""MIT. Copied mutation controls for the review packet. All mutations happen in a new
/var/tmp directory; the source packet is only read. Prints JSON results."""
import argparse, hashlib, importlib.util, json, os, shutil, tempfile
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, required=True, help='candidate MANIFEST.json bytes to install in copies')
    a = ap.parse_args()
    root = a.root.absolute()
    work = Path(tempfile.mkdtemp(prefix='t117q-proof-r1-controls-', dir='/var/tmp'))
    assert work.parts[:3] == ('/', 'var', 'tmp')
    spec = importlib.util.spec_from_file_location('review_verifier', root / 'verify.py')
    v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
    mbytes = a.manifest.read_bytes(); anchor = hashlib.sha256(mbytes).hexdigest()
    results = []
    reasons = {'wrong_anchor': 'external manifest anchor mismatch', 'changed_review': 'payload mismatch',
               'changed_verdict_resealed': 'external manifest anchor mismatch', 'missing_payload': 'exact file inventory mismatch',
               'extra_file': 'exact file inventory mismatch', 'extra_empty_directory': 'exact directory inventory mismatch',
               'root_symlink': 'symlink or nonregular', 'payload_symlink': 'symlink or nonregular',
               'payload_hardlink': 'hardlinked regular file', 'fifo': 'symlink or nonregular',
               'nested_manifest': 'nested manifest'}

    def run(name, mutation=None, wrong=False, rootlink=False):
        dest = work / name
        shutil.copytree(root, dest, symlinks=True)
        (dest / 'MANIFEST.json').write_bytes(mbytes)
        if mutation:
            mutation(dest)
        target = dest
        if rootlink:
            target = work / (name + '-link'); target.symlink_to(dest, target_is_directory=True)
        try:
            v.check(target, '0' * 64 if wrong else anchor); ok, why = True, 'PASS'
        except Exception as e:
            ok, why = False, str(e)
        expected = name == 'positive_copy'
        assert ok == expected, (name, ok, why)
        if not expected:
            assert reasons[name] in why, (name, why)
        results.append({'case': name, 'expected': 'accept' if expected else 'reject', 'actual': why})

    def reseal_verdict(d):
        f = d / 'review.md'; f.write_text(f.read_text().replace('PASS_FULL_T117Q', 'FAIL_T117Q'))
        m = json.loads((d / 'MANIFEST.json').read_text())
        for e in m['files']:
            if e['path'] == 'review.md':
                e['bytes'] = f.stat().st_size; e['sha256'] = hashlib.sha256(f.read_bytes()).hexdigest()
        (d / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')

    def payload_symlink(d):
        (d / 'reading-record.json').unlink(); (d / 'reading-record.json').symlink_to('review.md')

    def hardlink(d):
        (d / 'reading-record.json').unlink(); os.link(d / 'review.md', d / 'reading-record.json')

    try:
        run('positive_copy')
        run('wrong_anchor', wrong=True)
        run('changed_review', lambda d: (d / 'review.md').write_bytes((d / 'review.md').read_bytes() + b'x\n'))
        run('changed_verdict_resealed', reseal_verdict)
        run('missing_payload', lambda d: (d / 'reading-record.json').unlink())
        run('extra_file', lambda d: (d / 'extra.txt').write_text('extra'))
        run('extra_empty_directory', lambda d: (d / 'extra-empty').mkdir())
        run('root_symlink', rootlink=True)
        run('payload_symlink', payload_symlink)
        run('payload_hardlink', hardlink)
        run('fifo', lambda d: os.mkfifo(d / 'fifo'))
        run('nested_manifest', lambda d: (d / 'checks' / 'MANIFEST.json').write_text('{}'))
    finally:
        shutil.rmtree(work)
    return {'status': 'PASS', 'controls': results, 'candidate_manifest_sha256': anchor,
            'scope': 'Copied review packet in /var/tmp before the final review-controls record was added; '
                     'final sealed positive and wrong-anchor runs are reported outside the packet. No mathematical claim.'}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
