#!/usr/bin/env python3
"""MIT. Test integrity controls on DISPOSABLE COPIES; originals are read only.

Prints receipt JSON. The caller may redirect it into the owned package before
the final seal. No original manifest, payload or external anchor is written.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PACKAGE=Path(__file__).absolute().parents[1]
REPO=PACKAGE.parents[3]
OWNED=PACKAGE.relative_to(REPO)
AUTHOR=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r108')


def sha(body):
    return hashlib.sha256(body).hexdigest()


def all_hashes(base):
    return {p.relative_to(base).as_posix():sha(p.read_bytes())
            for p in base.rglob('*') if p.is_file() and not p.is_symlink()}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-sha256',required=True)
    parser.add_argument('--scratch-root',default=None,help='Optional disposable filesystem root')
    args=parser.parse_args()
    original_manifest=(PACKAGE/'manifest.json').read_bytes()
    assert sha(original_manifest)==args.expected_sha256
    manifest=json.loads(original_manifest)
    original_author=all_hashes(REPO/AUTHOR)
    original_review=all_hashes(PACKAGE)
    results=[]
    scenarios=['copied_positive','missing_external_digest','wrong_external_digest',
               'tampered_manifest','tampered_review_payload','tampered_author_proof',
               'tampered_source_blob','truncated_tree','unlisted_review_file',
               'unlisted_review_directory','symlink_payload','missing_primary_body',
               'extra_author_file','resealed_count_credit','resealed_unsafe_payload_path',
               'resealed_tree_incompleteness']
    with tempfile.TemporaryDirectory(prefix='t273nc108-review-controls-',dir=args.scratch_root) as scratch:
        root=Path(scratch)/'repo'
        for scenario in scenarios:
            if root.exists():
                shutil.rmtree(root)
            copied=root/OWNED
            shutil.copytree(PACKAGE,copied)
            # Exact author inventory is separately checked, so copy all of it.
            shutil.copytree(REPO/AUTHOR,root/AUTHOR)
            for row in manifest['external_anchors']:
                target=root/row['path']
                if not target.exists():
                    target.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copy2(REPO/row['path'],target)
            expected=args.expected_sha256
            mpath=copied/'manifest.json'
            if scenario=='wrong_external_digest':
                expected='0'*64
            elif scenario=='tampered_manifest':
                mpath.write_bytes(original_manifest+b'\n')
            elif scenario=='tampered_review_payload':
                p=copied/'public/review.md'; p.write_bytes(p.read_bytes()+b'\nCONTROL\n')
            elif scenario=='tampered_author_proof':
                p=root/AUTHOR/'public/author-proof.md'; p.write_bytes(p.read_bytes()+b'\nCONTROL\n')
            elif scenario=='tampered_source_blob':
                row=json.loads((copied/'private/provenance.json').read_bytes())['selected_source_blobs'][0]
                p=root/row['path']; p.write_bytes(p.read_bytes()+b'\nCONTROL\n')
            elif scenario in ('truncated_tree','resealed_tree_incompleteness'):
                p=root/'sources/preprints-tree.json'
                tree=json.loads(p.read_bytes()); tree['truncated']=True
                p.write_text(json.dumps(tree))
                if scenario.startswith('resealed'):
                    m=json.loads(original_manifest)
                    for row in m['external_anchors']:
                        if row['path']=='sources/preprints-tree.json':
                            row['bytes']=p.stat().st_size; row['sha256']=sha(p.read_bytes())
                    mpath.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
                    expected=sha(mpath.read_bytes())
            elif scenario=='unlisted_review_file':
                (copied/'unlisted.txt').write_text('CONTROL')
            elif scenario=='unlisted_review_directory':
                (copied/'unlisted-directory').mkdir()
            elif scenario=='symlink_payload':
                p=copied/'public/review.md'; p.unlink(); p.symlink_to(PACKAGE/'public/review.md')
            elif scenario=='missing_primary_body':
                (root/AUTHOR/'private/primary/2105.05627v2.html').unlink()
            elif scenario=='extra_author_file':
                (root/AUTHOR/'extra-control.txt').write_text('CONTROL')
            elif scenario=='resealed_count_credit':
                m=json.loads(original_manifest); m['count_change']=1
                mpath.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
                expected=sha(mpath.read_bytes())
            elif scenario=='resealed_unsafe_payload_path':
                m=json.loads(original_manifest)
                # Renaming an actual payload path to traversal fails inventory first.
                m['payloads'][0]['path']='../outside'
                mpath.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
                expected=sha(mpath.read_bytes())
            before=all_hashes(root)
            command=[sys.executable,'-B',str(copied/'public/verify.py')]
            if scenario!='missing_external_digest':
                command+=['--expected-sha256',expected]
            proc=subprocess.run(command,capture_output=True,text=True)
            after=all_hashes(root)
            success=proc.returncode==0
            assert success==(scenario=='copied_positive'),(scenario,proc.stdout,proc.stderr)
            assert before==after,'Verifier wrote files during '+scenario
            results.append({'scenario':scenario,'expected':'accept' if scenario=='copied_positive' else 'reject',
                            'exit_code':proc.returncode,'read_only_verified':True,
                            'observed':json.loads(proc.stdout) if success else proc.stderr.strip().splitlines()[-1]})
    assert original_author==all_hashes(REPO/AUTHOR),'original author changed'
    assert original_review==all_hashes(PACKAGE),'original review changed during controls'
    print(json.dumps({'status':'COPIED_CONTROLS_ONLY','tested_manifest_sha256':args.expected_sha256,
                      'controls':results,'original_author_preserved':True,'original_review_preserved':True,
                      'limits':'The receipt is included before the final seal. Resealed-copy controls test structural invariants with a new explicit detached digest; they are not accepted tampering against the original external anchor.'},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
