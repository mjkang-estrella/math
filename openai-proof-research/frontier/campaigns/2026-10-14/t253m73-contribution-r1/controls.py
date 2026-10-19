#!/usr/bin/env python3
"""MIT. Copied positive/negative integrity fixtures, created only inside this packet."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(b):
    return hashlib.sha256(b).hexdigest()


def run():
    root = Path(__file__).absolute().parent
    evidence = json.loads((root/'external-evidence.json').read_bytes())
    repo = Path(evidence['repo_root'])
    outcomes = {}
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=root) as temp:
        work = Path(temp)
        copied_repo = work/'repository'
        # Third-party copies are temporary private control data, never public artifacts.
        for r in evidence['fixed_files']:
            dest = copied_repo/r['path']
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(repo/r['path'], dest)
        fixture = work/'fixture'
        fixture.mkdir()
        for name in ('verify.py', 'external-evidence.json', 'verdict.json'):
            shutil.copyfile(root/name, fixture/name)
        (fixture/'payload.txt').write_text('Original synthetic control payload.\n')

        def seal(folder):
            files = []
            for p in sorted(folder.iterdir()):
                if p.name in ('manifest.json', 'manifest.sha256'):
                    continue
                b = p.read_bytes()
                files.append({'path': p.name, 'bytes': len(b), 'sha256': sha(b)})
            m = {'schema': 't253m73-contribution-r1-v1', 'target': 'T253M73',
                 'pinned_revision': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                 'author_manifest_sha256': evidence['author_manifest_sha256'],
                 'frozen_scope_sha256': evidence['scope_sha256'],
                 'canonical_tree_sha256': evidence['canonical_tree_sha256'],
                 'conditional_contribution_verdict': 'TECHNICAL',
                 'correctness_gate': 'NOT_PERFORMED', 'campaign_credit': 0,
                 'directories': [], 'files': files}
            raw = (json.dumps(m, indent=2)+'\n').encode()
            (folder/'manifest.json').write_bytes(raw)
            anchor = sha(raw)
            (folder/'manifest.sha256').write_text(anchor+'\n')
            return anchor

        anchor = seal(fixture)

        def execute(folder, supplied=anchor, include=True):
            cmd = [sys.executable, '-B', str(folder/'verify.py'), '--repo-root', str(copied_repo)]
            if include:
                cmd += ['--expected-manifest-sha256', supplied]
            result = subprocess.run(cmd, text=True, capture_output=True)
            return result.returncode, result.stdout.strip(), result.stderr.strip()

        rc, out, _ = execute(fixture)
        assert rc == 0, out
        outcomes['copied_positive_with_all_external_files'] = 'accepted'
        for name in ('missing_detached_anchor', 'wrong_detached_anchor', 'changed_payload',
                     'missing_payload', 'extra_file', 'extra_empty_directory', 'symlink_payload',
                     'hardlink_payload', 'wrong_sidecar', 'changed_manifest',
                     'self_resealed_with_original_detached_anchor',
                     'count_inflation_with_new_fixture_anchor',
                     'false_correctness_pass_with_new_fixture_anchor',
                     'changed_author_anchor_with_new_fixture_anchor', 'duplicate_inventory_path'):
            case = work/name
            shutil.copytree(fixture, case)
            supplied = anchor
            include = True
            if name == 'missing_detached_anchor':
                include = False
            elif name == 'wrong_detached_anchor':
                supplied = '0'*64
            elif name == 'changed_payload':
                (case/'payload.txt').write_text('tampered\n')
            elif name == 'missing_payload':
                (case/'payload.txt').unlink()
            elif name == 'extra_file':
                (case/'extra.txt').write_text('extra\n')
            elif name == 'extra_empty_directory':
                (case/'extra').mkdir()
            elif name == 'symlink_payload':
                (case/'payload.txt').unlink()
                (case/'payload.txt').symlink_to(fixture/'payload.txt')
            elif name == 'hardlink_payload':
                (case/'payload.txt').unlink()
                (case/'payload.txt').hardlink_to(fixture/'payload.txt')
            elif name == 'wrong_sidecar':
                (case/'manifest.sha256').write_text('0'*64+'\n')
            elif name in ('changed_manifest', 'self_resealed_with_original_detached_anchor'):
                (case/'manifest.json').write_bytes((case/'manifest.json').read_bytes()+b' ')
                if name.startswith('self_resealed'):
                    (case/'manifest.sha256').write_text(sha((case/'manifest.json').read_bytes())+'\n')
            elif name in ('count_inflation_with_new_fixture_anchor', 'false_correctness_pass_with_new_fixture_anchor'):
                v = json.loads((case/'verdict.json').read_bytes())
                if name.startswith('count'):
                    v['campaign_credit'] = 1
                else:
                    v['correctness_gate'] = 'PASS'
                (case/'verdict.json').write_text(json.dumps(v)+'\n')
                supplied = seal(case)
            elif name == 'changed_author_anchor_with_new_fixture_anchor':
                ev = json.loads((case/'external-evidence.json').read_bytes())
                ev['author_manifest_sha256'] = '0'*64
                (case/'external-evidence.json').write_text(json.dumps(ev)+'\n')
                supplied = seal(case)
            elif name == 'duplicate_inventory_path':
                m = json.loads((case/'manifest.json').read_bytes())
                m['files'].append(m['files'][0])
                raw = (json.dumps(m)+'\n').encode()
                (case/'manifest.json').write_bytes(raw)
                supplied = sha(raw)
                (case/'manifest.sha256').write_text(supplied+'\n')
            rc, out, err = execute(case, supplied, include)
            assert rc != 0, name
            outcomes[name] = 'rejected'
            if name == 'hardlink_payload':
                (case/'payload.txt').unlink()
        # Only these copied external bytes are mutated, then restored.
        for label, rel in (
            ('changed_copied_author_candidate', evidence['author_root']+'/candidate.md'),
            ('changed_copied_frozen_scope', evidence['author_root']+'/scope-T253M73.md'),
            ('changed_copied_primary_text', evidence['author_root']+'/private/primary/Li2209.08087v2.txt'),
            ('changed_copied_canonical_tree', 'sources/preprints-tree.json')):
            p = copied_repo/rel
            old = p.read_bytes()
            p.write_bytes(old+b'\n')
            rc, out, _ = execute(fixture)
            assert rc != 0, label
            outcomes[label] = 'rejected'
            p.write_bytes(old)
        extra = copied_repo/evidence['author_root']/'extra-private-file.txt'
        extra.write_text('unlisted\n')
        assert execute(fixture)[0] != 0
        outcomes['extra_copied_author_file'] = 'rejected'
        extra.unlink()
        assert execute(fixture)[0] == 0
        outcomes['restored_copied_positive'] = 'accepted'

        author_control = work/'private-author-control-replay'
        author_control.mkdir()
        for name in ('verify.py', 'controls.py'):
            shutil.copyfile(repo/evidence['author_root']/name, author_control/name)
        replay = subprocess.run([sys.executable, '-B', str(author_control/'controls.py')],
                                text=True, capture_output=True)
        assert replay.returncode == 0, replay.stderr
        author_outcomes = json.loads(replay.stdout)
    return {'scope': 'Copied integrity fixtures only; no mathematics/acceptance evidence.',
            'review_verifier_controls': outcomes,
            'author_controls_replayed_only_on_private_copies': author_outcomes,
            'temporary_control_copies_removed': True,
            'self_resealed_limit': 'The original-detached-anchor test checks tamper authentication. Separate newly anchored synthetic verdict tests exercise explicit gate/count guards; neither establishes mathematical truth.',
            'campaign_credit': 0}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
