#!/usr/bin/env python3
"""Exercise the release boundary without creating an archive or a real PASS gate.
Copyright 2026 Myeongjin Kang; MIT.
"""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import collect, manifest_for
from verify_bundle import verify
from release_common import (RELEASE, REVIEW, PARENT, MANUSCRIPT, FROZEN_HASHES,
                            check_record, discover_root, read_regular, record,
                            run_finite_checks, safe_name, validate_gate)


def main():
    root = discover_root(Path(__file__).resolve().parent)
    results = {}

    def rejected(name, operation):
        try:
            operation()
        except (ValueError, FileNotFoundError, KeyError, TypeError):
            results[name] = True
        else:
            raise AssertionError('Expected rejection: '+name)

    gate_path = RELEASE+'/gate.json'
    selected, gate = collect(root, gate_path, require_integrated=False)
    if gate['state'] != 'pending':
        raise ValueError('Preparation checks require the real pending template')
    results['frozen_allowlist_hashes_and_lengths'] = True
    rejected('pending_gate_rejected', lambda:collect(root, gate_path))
    rejected('PASS_substring_is_not_a_gate', lambda:validate_gate(root,
        {**gate, 'state':'PASS in review text'}, FROZEN_HASHES, True))
    rejected('integrated_label_without_trust_anchor_rejected', lambda:validate_gate(root,
        {**gate, 'state':'integrated'}, FROZEN_HASHES, True))
    rejected('wrong_frozen_binding_rejected', lambda:validate_gate(root,
        {**gate, 'bound_manuscript':{}}, FROZEN_HASHES, False))
    for path in ['../escape', '/absolute', 'a/../escape', 'a//b', 'a\\b', 'a:b', 'a/./b']:
        rejected('unsafe_path:'+path, lambda p=path:safe_name(p))
    finite = run_finite_checks(root)
    results['four_finite_program_receipts_identical'] = True
    manifest = manifest_for(selected, gate_path, gate, finite, None)
    # This is a disposable extracted-layout preparation tree, never a ZIP and
    # never a synthetic approval. The actual pending template stays pending.
    with tempfile.TemporaryDirectory(prefix='kinetic-preparation-') as directory:
        temp = Path(directory)
        # Negative-only gate fixture: the real pre-gate parent authentication
        # cannot be promoted by supplying a review whose text contains PASS.
        # No positive disposition or manuscript acceptance is manufactured.
        fixture = temp/'negative-gate'
        fixture.mkdir()
        fixture_data = {
            REVIEW+'/review.md':b'Negative test only: PASS text supplies no authority.\n',
            REVIEW+'/provenance.json':b'{"test_fixture": true}\n',
            PARENT+'/manuscript-authentication.json':read_regular(root, PARENT+'/manuscript-authentication.json'),
        }
        review_rows = [record(name, data) for name, data in fixture_data.items()
                       if name.startswith(REVIEW+'/')]
        fixture_data[REVIEW+'/outputs.json'] = (json.dumps({'files':review_rows})+'\n').encode()
        for name, data in fixture_data.items():
            path = fixture/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        pretend = {**gate, 'state':'integrated',
                   'review':record(REVIEW+'/review.md', fixture_data[REVIEW+'/review.md']),
                   'review_manifest':record(REVIEW+'/outputs.json', fixture_data[REVIEW+'/outputs.json']),
                   'reviewer_record':record(REVIEW+'/provenance.json', fixture_data[REVIEW+'/provenance.json']),
                   'parent_disposition':record(PARENT+'/manuscript-authentication.json',
                                              fixture_data[PARENT+'/manuscript-authentication.json']),
                   'reviewer':{'provider':'negative fixture', 'model':'negative fixture', 'task_id':'negative fixture'}}
        anchor = pretend['parent_disposition']['sha256']
        rejected('pre_gate_parent_receipt_cannot_authorize_PASS_text',
                 lambda:validate_gate(fixture, pretend, FROZEN_HASHES, True, anchor))
        rejected('wrong_parent_trust_anchor_rejected',
                 lambda:validate_gate(fixture, pretend, FROZEN_HASHES, True, '0'*64))
        tree = temp/'tree'
        tree.mkdir()
        for name, data in selected.items():
            target = tree/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        (tree/'BUNDLE-MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
        clean = verify(tree, preparation=True)
        results['clean_extracted_preparation_tree'] = clean['gate_state']=='pending'
        run = subprocess.run([sys.executable, '-I', str(tree/RELEASE/'verify_bundle.py'),
                              '--preparation'], capture_output=True, text=True, timeout=360)
        if run.returncode != 0 or json.loads(run.stdout)['gate_state'] != 'pending':
            raise AssertionError('Extracted command failed: '+run.stderr)
        results['extracted_CLI_without_author_checkout_or_bytecode_writes'] = True
        rejected('production_verifier_rejects_pending_tree', lambda:verify(tree))
        extra = tree/'unlisted.txt'
        extra.write_text('not a member')
        rejected('unlisted_file_rejected', lambda:verify(tree, preparation=True))
        extra.unlink()
        (tree/'unexpected-empty-directory').mkdir()
        rejected('unlisted_directory_rejected', lambda:verify(tree, preparation=True))
        (tree/'unexpected-empty-directory').rmdir()
        row = manifest['files'][0]
        target = tree/row['path']
        original = target.read_bytes()
        target.write_bytes(original+b'changed')
        rejected('tampered_hash_or_length_rejected', lambda:verify(tree, preparation=True))
        target.unlink()
        target.symlink_to(root/row['path'])
        rejected('file_symlink_rejected', lambda:verify(tree, preparation=True))
        target.unlink()
        target.write_bytes(original)
        receipt = tree/MANUSCRIPT/'checks/repair_checks.json'
        receipt_bytes = receipt.read_bytes()
        receipt.write_bytes(receipt_bytes+b' ')
        rejected('changed_finite_receipt_rejected', lambda:run_finite_checks(tree))
        receipt.write_bytes(receipt_bytes)
        # Check a parent-directory symlink independently of the inventory.
        (temp/'linked-parent').symlink_to(tree, target_is_directory=True)
        rejected('directory_symlink_rejected', lambda:check_record(temp,
            {**row, 'path':'linked-parent/'+row['path']}))
        out = temp/'must-not-exist.zip'
        run = subprocess.run([sys.executable, '-I', str(root/RELEASE/'assemble.py'),
                              str(out), '--project-root', str(root)], capture_output=True, text=True)
        if run.returncode == 0 or out.exists() or 'Manuscript gate pending' not in run.stderr:
            raise AssertionError('Pending assembly did not fail safely: '+run.stderr)
        results['assembler_pending_failure_creates_no_archive'] = True
    print(json.dumps({'status':'PREPARATION MACHINERY CHECKS PASSED; manuscript gate pending',
                      'checks':results, 'finite_checks':finite, 'archive_created':False,
                      'approval_or_acceptance':False}, indent=2))


if __name__ == '__main__':
    main()
