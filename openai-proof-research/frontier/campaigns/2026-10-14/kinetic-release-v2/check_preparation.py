#!/usr/bin/env python3
"""Disposable preparation/mutation checks, never a final gate or publication.
Copyright 2026 Myeongjin Kang; MIT.
"""
from pathlib import Path
import copy
import json
import os
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from assemble import collect, manifest_for, write_archive
from bind_gate import build_config
from verify_bundle import verify
from release_common import (RELEASE, MANUSCRIPT, ORIGINAL_REVIEW, FROZEN_HASHES,
    check_record, check_freeze, discover_root, read_regular, read_json, record,
    run_finite_checks, safe_name, validate_gate, manifest_records, decode_json, sha)


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
    assert gate['state'] == 'pending'
    results['all_selected_hashes_lengths_and_57_corrected_outputs'] = True
    results['exact_original_to_corrected_TeX_diff_reproduced'] = True
    # Local baseline: the old release is read-only historical input, not copied
    # into the package. The two reused files retain their original bytes.
    provenance = read_json(root, RELEASE+'/implementation-provenance.json')
    for row in provenance['historical_release_authenticated']:
        check_record(root, row)
    results['entire_old_release_unchanged_from_preparation_baseline'] = True
    for item in provenance['reused_byte_identically']:
        assert check_record(root, item['source']) == read_regular(root, item['destination'])
    results['Lean_rebuild_program_and_receipt_reused_byte_identically'] = True
    historical_parent = 'frontier/campaigns/2026-10-14/kinetic-parent/manuscript-authentication.json'
    rejected('pre_gate_parent_cannot_build_final_config', lambda:build_config(root,
        historical_parent, sha(read_regular(root,historical_parent)), []))
    rejected('config_builder_rejects_wrong_parent_anchor', lambda:build_config(root,
        historical_parent, '0'*64, []))
    rejected('pending_gate_rejected', lambda:collect(root, gate_path))
    rejected('PASS_substring_is_not_a_gate', lambda:validate_gate(root,
        {**gate, 'state':'PASS in review text'}, FROZEN_HASHES, True))
    rejected('integrated_label_without_trust_anchor_rejected', lambda:validate_gate(root,
        {**gate, 'state':'integrated'}, FROZEN_HASHES, True))
    rejected('integrated_label_without_actual_identity_rejected', lambda:validate_gate(root,
        {**gate, 'state':'integrated'}, FROZEN_HASHES, True, '0'*64))
    rejected('wrong_frozen_binding_rejected', lambda:validate_gate(root,
        {**gate, 'bound_manuscript':{}}, FROZEN_HASHES, False))
    rejected('old_manuscript_path_rejected', lambda:validate_gate(root,
        {**gate, 'manuscript_path':MANUSCRIPT.replace('-consolidation','')}, FROZEN_HASHES, False))
    rejected('anticipated_record_in_pending_gate_rejected', lambda:validate_gate(root,
        {**gate, 'review':{}}, FROZEN_HASHES, False))
    rejected('v1_gate_schema_rejected', lambda:validate_gate(root,
        {**gate, 'schema':'kinetic-release-gate-v1'}, FROZEN_HASHES, False))
    for path in ['../escape', '/absolute', 'a/../escape', 'a//b', 'a\\b', 'a:b', 'a/./b', '.', 'a\x00b']:
        rejected('unsafe_path:'+repr(path), lambda p=path:safe_name(p))
    # Real historical review rows, not a fabricated final review/identity.
    actual = read_json(root, ORIGINAL_REVIEW+'/outputs.json')
    full = manifest_records(actual, ORIGINAL_REVIEW)
    relative = [{**row, 'path':name[len(ORIGINAL_REVIEW)+1:]} for name,row in full.items()]
    for shape in [relative, {'files':relative}, {'outputs':relative}]:
        assert manifest_records(shape, ORIGINAL_REVIEW) == full
    results['real_review_outputs_schema_and_all_three_supported_shapes'] = True
    one = relative[0]
    rejected('relative_full_normalized_duplicate_rejected', lambda:manifest_records(
        [one, full[ORIGINAL_REVIEW+'/'+one['path']]], ORIGINAL_REVIEW))
    rejected('ambiguous_manifest_keys_rejected', lambda:manifest_records({'files':[], 'outputs':[]}))
    rejected('missing_manifest_key_rejected', lambda:manifest_records({'inputs':[]}))
    rejected('nonlist_manifest_rejected', lambda:manifest_records({'files':{}}))
    rejected('foreign_project_path_rejected', lambda:manifest_records(
        [{**one,'path':'frontier/elsewhere/review.md'}], ORIGINAL_REVIEW))
    rejected('manifest_traversal_rejected', lambda:manifest_records([{**one,'path':'../review.md'}], ORIGINAL_REVIEW))
    rejected('boolean_length_rejected', lambda:manifest_records([{**one,'bytes':True}]))
    rejected('malformed_digest_rejected', lambda:manifest_records([{**one,'sha256':'bad'}]))
    rejected('extra_record_field_rejected', lambda:manifest_records([{**one,'extra':0}]))
    rejected('duplicate_JSON_keys_rejected', lambda:decode_json('{"files":[],"files":[]}'))
    finite = run_finite_checks(root)
    assert len(finite) == 5
    results['five_finite_program_receipts_identical_in_disposable_copies'] = True
    manifest = manifest_for(selected, gate_path, gate, finite, None)
    with tempfile.TemporaryDirectory(prefix='kinetic-v2-preparation-') as directory:
        temp = Path(directory)
        tree = temp/'tree'
        tree.mkdir()
        for name, data in selected.items():
            target = tree/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        manifest_path = tree/'BUNDLE-MANIFEST.json'
        def save(value): manifest_path.write_text(json.dumps(value, indent=2)+'\n')
        save(manifest)
        assert verify(tree, preparation=True)['gate_state']=='pending'
        results['clean_extracted_preparation_tree'] = True
        run = subprocess.run([sys.executable, '-I', str(tree/RELEASE/'verify_bundle.py'),
                              '--preparation'], capture_output=True, text=True, timeout=360)
        if run.returncode != 0 or json.loads(run.stdout)['gate_state'] != 'pending':
            raise AssertionError('Extracted command failed: '+run.stderr)
        results['extracted_CLI_without_checkout_or_bytecode_writes'] = True
        rejected('production_verifier_rejects_pending_tree', lambda:verify(tree))
        rejected('wrong_external_manifest_hash_rejected', lambda:verify(tree, True, '0'*64))
        rejected('wrong_external_parent_hash_rejected', lambda:verify(tree, True, None, '0'*64))
        changed = copy.deepcopy(manifest); changed['author_names']=['wrong']
        save(changed)
        rejected('changed_manifest_metadata_rejected', lambda:verify(tree, True))
        save(manifest)
        changed = copy.deepcopy(manifest); changed['files'].append(changed['files'][0])
        save(changed)
        rejected('duplicate_bundle_member_rejected', lambda:verify(tree, True))
        save(manifest)
        extra = tree/'unlisted.txt'; extra.write_text('not a member')
        rejected('unlisted_file_rejected', lambda:verify(tree, True)); extra.unlink()
        extra = tree/'unexpected-empty-directory'; extra.mkdir()
        rejected('unlisted_directory_rejected', lambda:verify(tree, True)); extra.rmdir()
        extra = tree/'fifo'; os.mkfifo(extra)
        rejected('nonregular_file_rejected', lambda:verify(tree, True)); extra.unlink()
        row = manifest['files'][0]; target = tree/row['path']; original = target.read_bytes()
        target.write_bytes(original+b'changed')
        rejected('tampered_hash_or_length_rejected', lambda:verify(tree, True))
        target.unlink(); target.symlink_to(root/row['path'])
        rejected('file_symlink_rejected', lambda:verify(tree, True))
        target.unlink(); target.write_bytes(original)
        receipt = tree/MANUSCRIPT/'checks/repair_checks.json'; data=receipt.read_bytes()
        receipt.write_bytes(data+b' ')
        rejected('changed_finite_receipt_rejected', lambda:run_finite_checks(tree))
        receipt.write_bytes(data)
        target = tree/MANUSCRIPT/'inputs.json'; data=target.read_bytes(); target.write_bytes(data+b' ')
        rejected('changed_corrected_input_manifest_rejected', lambda:check_freeze(tree)); target.write_bytes(data)
        (temp/'linked-parent').symlink_to(tree, target_is_directory=True)
        rejected('directory_symlink_rejected', lambda:check_record(temp,{**row,'path':'linked-parent/'+row['path']}))
        # Exercise the actual deterministic writer with a pending, explicitly
        # nonpublication manifest. Both ZIPs and extraction disappear on exit.
        z1=write_archive(temp/'PREPARATION-ONLY-1.zip',selected,manifest)
        z2=write_archive(temp/'PREPARATION-ONLY-2.zip',selected,manifest)
        assert z1.read_bytes()==z2.read_bytes()
        results['deterministic_temporary_preparation_ZIP_bytes'] = True
        extracted=temp/'from-zip'
        with zipfile.ZipFile(z1) as archive: archive.extractall(extracted)
        assert verify(extracted, True)['gate_state']=='pending'
        results['temporary_ZIP_exact_membership_CRC_bytes_and_extracted_verification'] = True
        rejected('archive_no_overwrite', lambda:write_archive(z1,selected,manifest))
        link=temp/'link.zip'; link.symlink_to(z1)
        rejected('archive_symlink_destination_rejected', lambda:write_archive(link,selected,manifest))
        rejected('archive_symlink_parent_rejected', lambda:write_archive(temp/'linked-parent/a.zip',selected,manifest))
        rejected('archive_missing_parent_rejected', lambda:write_archive(temp/'missing/a.zip',selected,manifest))
        out=temp/'must-not-exist.zip'
        run=subprocess.run([sys.executable,'-I',str(root/RELEASE/'assemble.py'),str(out),
                            '--project-root',str(root)],capture_output=True,text=True,timeout=360)
        if run.returncode==0 or out.exists() or 'Manuscript gate pending' not in run.stderr:
            raise AssertionError('Pending assembly did not fail safely: '+run.stderr)
        results['publication_CLI_pending_failure_creates_no_archive'] = True
    print(json.dumps({'status':'PREPARATION MACHINERY CHECKS PASSED; corrected-edition gate pending',
        'checks':results,'finite_checks':finite,'temporary_preparation_ZIPs_created_and_deleted':2,
        'persistent_archive_created':False,'actual_final_review_read':False,
        'positive_integrated_gate_end_to_end_tested':False,'approval_or_acceptance':False},indent=2))


if __name__ == '__main__':
    main()
