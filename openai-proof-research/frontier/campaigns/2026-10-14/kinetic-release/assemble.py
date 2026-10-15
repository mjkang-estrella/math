#!/usr/bin/env python3
"""Allowlisted local assembly; no submission. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path
import argparse
import json
import sys
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from release_common import (CAMPAIGN, RELEASE, MANUSCRIPT, FROZEN_HASHES, SCOPE,
    FORMAL_SCOPE, check_record, check_freeze, discover_root, excluded_payload,
    read_json, read_regular, record, sha, validate_gate, run_finite_checks)


def collect(root, gate_path, trusted_parent_sha256=None, require_integrated=True):
    check_freeze(root)
    selected = {}
    for inventory in [RELEASE+'/allowlist.json', RELEASE+'/outputs.json']:
        data = read_regular(root, inventory)
        rows = json.loads(data)['files']
        for row in rows:
            name = row['path']
            if (name in selected and name != RELEASE+'/allowlist.json') or excluded_payload(name):
                raise ValueError('Duplicate or excluded allowlist member: '+name)
            selected[name] = check_record(root, row)
        if inventory in selected:
            raise ValueError('Inventory must not hash itself')
        selected[inventory] = data
    gate_bytes = read_regular(root, gate_path)
    gate = json.loads(gate_bytes)
    selected.update(validate_gate(root, gate, FROZEN_HASHES, require_integrated,
                                  trusted_parent_sha256))
    if gate_path in selected and selected[gate_path] != gate_bytes:
        raise ValueError('Gate config conflicts with frozen inventory')
    selected[gate_path] = gate_bytes
    if not gate_path.startswith(CAMPAIGN+'/kinetic-') or excluded_payload(gate_path):
        raise ValueError('Gate config must be an allowed kinetic campaign record')
    return selected, gate


def manifest_for(selected, gate_path, gate, finite, trusted_parent_sha256):
    return {
        'schema':'kinetic-local-bundle-v1',
        'status': ('LOCAL PUBLICATION PACKAGE; NOT SUBMITTED' if gate['state'] == 'integrated'
                   else 'PREPARATION CHECK ONLY; MANUSCRIPT GATE PENDING'),
        'gate_state':gate['state'], 'gate_path':gate_path,
        'trusted_parent_disposition_sha256':trusted_parent_sha256,
        'bound_manuscript':FROZEN_HASHES,
        'author_names':['Myeongjin Kang'], 'affiliations':[],
        'original_prose_license':'CC-BY-4.0', 'original_code_license':'MIT',
        'third_party_rights':'Retained; external raw manuscripts and dependency caches excluded.',
        'theorem_scope':SCOPE, 'formal_scope':FORMAL_SCOPE,
        'full_analytic_or_Lean_certificate':False, 'public_submission':False,
        'finite_checks':finite,
        'files':[record(name, data) for name, data in sorted(selected.items())],
        'integrity_note':'Hashes are integrity bindings, not signatures or proof certificates. '
                         'Obtain the archive/manifest and parent hash from a trusted source.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--project-root', type=Path)
    parser.add_argument('--gate', default=RELEASE+'/gate.json', help='project-relative parent config')
    parser.add_argument('--parent-disposition-sha256', help='independently trusted parent hash')
    parser.add_argument('--check', action='store_true', help='audit preparation; write no archive')
    args = parser.parse_args()
    root = args.project_root or discover_root(Path(__file__).resolve().parent)
    if args.check == (args.output is not None):
        parser.error('choose --check with no output, or supply an output archive')
    selected, gate = collect(root, args.gate, args.parent_disposition_sha256,
                             require_integrated=not args.check)
    finite = run_finite_checks(root)
    for name, data in selected.items():
        if read_regular(root, name) != data:
            raise ValueError('Concurrent input change: '+name)
    manifest = manifest_for(selected, args.gate, gate, finite, args.parent_disposition_sha256)
    if args.check:
        print(json.dumps({'status':manifest['status'], 'files':len(selected),
                          'finite_checks':finite, 'archive_created':False}, indent=2))
        return
    destination = args.output.absolute()
    # Exclusive creation; never replace an existing file or follow an output symlink.
    if destination.exists() or destination.is_symlink():
        raise ValueError('Refusing to replace destination: '+str(destination))
    if not destination.parent.is_dir():
        raise ValueError('Output parent directory must already exist')
    if any(path.is_symlink() for path in [destination.parent, *destination.parent.parents]):
        raise ValueError('Symlink output directory is not allowed')
    selected['BUNDLE-MANIFEST.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    created = False
    try:
        with destination.open('xb') as stream:
            created = True
            with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
                for name, data in sorted(selected.items()):
                    info = zipfile.ZipInfo(name, date_time=(2026, 10, 14, 0, 0, 0))
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.external_attr = 0o100644 << 16
                    archive.writestr(info, data)
        with zipfile.ZipFile(destination) as archive:
            if archive.testzip() or set(archive.namelist()) != set(selected):
                raise ValueError('Archive membership/CRC failure')
            for name, data in selected.items():
                if archive.read(name) != data:
                    raise ValueError('Archive bytes differ: '+name)
    except Exception:
        # Only remove the partial archive created by this invocation.
        if created:
            destination.unlink(missing_ok=True)
        raise
    print(json.dumps({'archive':str(destination), 'sha256':sha(destination.read_bytes()),
                      'files':len(manifest['files']), 'status':manifest['status']}, indent=2))


if __name__ == '__main__':
    main()
