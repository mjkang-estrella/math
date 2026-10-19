#!/usr/bin/env python3
"""Run integrity controls on disposable COPIES inside the assigned directory.

Read before executing. Never mutates author or other external files. Temp copies
are removed on exit. JSON receipts go to stdout; this script saves no results.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

AUTHOR_HASH = '231ee8b0520af882eeb1c2fa1c680ff2fa32f3999345778223f7eb97a5edc5f5'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def call(packet, repo, expected, success):
    result = subprocess.run([sys.executable, '-B', str(packet/'verify.py'),
                             '--repo-root', str(repo), '--expected-sha256', expected],
                            text=True, capture_output=True)
    assert (result.returncode == 0) == success, (result.stdout, result.stderr)
    report = json.loads(result.stdout if success else result.stderr)
    return report


def save_manifest(packet, manifest):
    data = (json.dumps(manifest, indent=2, sort_keys=True)+'\n').encode()
    (packet/'manifest.json').write_bytes(data)
    return digest(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind', choices=['author', 'review'])
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    repo = root.parents[3]
    author = root.parent/'fresh-structural-discovery-r109'
    result = {'kind': args.kind, 'scope': 'Integrity only, on temporary copies; no mathematical verdict.'}
    # For a self-copy, list payloads BEFORE creating the temporary child.
    current_files = [p for p in root.rglob('*') if p.is_file()]
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=root/'private') as tmp:
        temp = Path(tmp)
        packet = temp/'packet'
        if args.kind == 'author':
            shutil.copytree(author, packet)
            expected = AUTHOR_HASH
            result['positive'] = call(packet, repo, expected, True)
            result['wrong_anchor'] = call(packet, repo, '0'*64, False)
            p = packet/'public/proof.md'
            original = p.read_bytes()
            p.write_bytes(bytes([original[0] ^ 1])+original[1:])
            result['same_size_body_mutation'] = call(packet, repo, expected, False)
            p.write_bytes(original)
            extra = packet/'unexpected-control.txt'
            extra.write_text('unexpected\n')
            result['unexpected_file'] = call(packet, repo, expected, False)
            extra.unlink()
            manifest_raw = (packet/'manifest.json').read_bytes()
            m = json.loads(manifest_raw)
            m['accepted'] = True
            counterfeit_hash = save_manifest(packet, m)
            result['counterfeit_acceptance_with_new_anchor'] = call(packet, repo, counterfeit_hash, False)
            (packet/'manifest.json').write_bytes(manifest_raw)
            result['restored_copy'] = call(packet, repo, expected, True)
        else:
            packet.mkdir()
            for p in current_files:
                target = packet/p.relative_to(root)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, target)
            expected = digest((packet/'manifest.json').read_bytes())
            result['provisional_review_anchor'] = expected
            result['positive'] = call(packet, repo, expected, True)
            result['wrong_anchor'] = call(packet, repo, '0'*64, False)
            p = packet/'review.md'
            original = p.read_bytes()
            p.write_bytes(bytes([original[0] ^ 1])+original[1:])
            result['same_size_review_mutation'] = call(packet, repo, expected, False)
            p.write_bytes(original)
            extra = packet/'unexpected-control.txt'
            extra.write_text('unexpected\n')
            result['unexpected_file'] = call(packet, repo, expected, False)
            extra.unlink()
            manifest_raw = (packet/'manifest.json').read_bytes()
            m = json.loads(manifest_raw)
            m['correctness_gate'] = 'PASS'
            result['counterfeit_correctness_with_new_anchor'] = call(packet, repo, save_manifest(packet, m), False)
            (packet/'manifest.json').write_bytes(manifest_raw)
            # Clone only the anchored input files, not a repository snapshot.
            context = temp/'context'
            m = json.loads(manifest_raw)
            for item in m['external_inputs']:
                target = context/item['path']
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(repo/item['path'], target)
            result['copied_context_positive'] = call(packet, context, expected, True)
            tree = context/'sources/preprints-tree.json'
            original_tree = tree.read_bytes()
            t = json.loads(original_tree)
            t['truncated'] = True
            replacement = (json.dumps(t)+'\n').encode()
            tree.write_bytes(replacement)
            result['copied_context_mutation'] = call(packet, context, expected, False)
            # Even changing the local manifest and passing its new hash must not
            # turn a declared truncated tree into acceptable provenance.
            for item in m['external_inputs']:
                if item['path'] == 'sources/preprints-tree.json':
                    item['bytes'] = len(replacement)
                    item['sha256'] = digest(replacement)
            result['reanchored_truncated_tree'] = call(packet, context, save_manifest(packet, m), False)
            tree.write_bytes(original_tree)
            (packet/'manifest.json').write_bytes(manifest_raw)
            result['restored_copy'] = call(packet, repo, expected, True)
    result['temporary_copies_removed'] = True
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
