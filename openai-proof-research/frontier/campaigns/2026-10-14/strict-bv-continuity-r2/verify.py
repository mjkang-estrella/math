#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT license.
"""Read-only sealed authentication BEFORE executing any stored code."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys


PRIOR_SEAL = '0141a77c195a33b988dea9621bbf45577414b22ed0d8a0723c436a665764bc24'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    data = path.read_bytes()
    return {'bytes':len(data), 'sha256':hashlib.sha256(data).hexdigest()}


def authenticate(root):
    # The externally supplied --seal-sha256 is authoritative when present;
    # otherwise use the local detached convenience copy for self-checking.
    args = sys.argv[1:]
    if args:
        require(len(args)==2 and args[0]=='--seal-sha256', 'usage: verify.py [--seal-sha256 HEX]')
        expected_seal = args[1]
    else:
        expected_seal = (root/'seal.sha256').read_text().strip()
    require(len(expected_seal)==64 and all(c in '0123456789abcdef' for c in expected_seal),
            'invalid expected detached seal')
    require(not (root/'seal.json').is_symlink(), 'seal symlink prohibited')
    require(digest(root/'seal.json')['sha256']==expected_seal, 'detached seal mismatch')
    require((root/'seal.sha256').read_text()==expected_seal+'\n', 'local detached seal mismatch')
    seal = json.loads((root/'seal.json').read_text())
    inventories = []
    for inventory, want in seal['inventories'].items():
        require(not (root/inventory).is_symlink(), 'inventory symlink prohibited')
        require(digest(root/inventory)==want, 'inventory authentication failed: '+inventory)
        inventories.append(json.loads((root/inventory).read_text()))
    files = {}
    for inventory in inventories:
        for name, want in inventory['files'].items():
            rel = Path(name)
            require(not rel.is_absolute() and '..' not in rel.parts, 'invalid inventory path')
            require(name not in files, 'duplicate inventory membership')
            path = root/rel
            require(path.is_file() and not path.is_symlink(), 'missing/nonregular file: '+name)
            require(digest(path)==want, 'content authentication failed: '+name)
            files[name] = want
    expected = set(files) | set(seal['inventories']) | {'seal.json','seal.sha256'}
    actual = set()
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'symlinks prohibited anywhere in package')
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    require(actual==expected, 'inventory membership mismatch: '+str(sorted(actual^expected)))
    prior = root/'inputs/private/frozen-r5'
    require(digest(prior/'seal.json')['sha256']==PRIOR_SEAL, 'frozen prior detached seal mismatch')
    prior_report = (prior/'candidate.md').read_bytes()
    require((root/'assignment-and-history.md').read_bytes().endswith(prior_report),
            'appended prior report is not verbatim')
    return len(files), expected_seal


def replay(root, command, receipt):
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    completed = subprocess.run(command, cwd=root, env=environment,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    require(completed.returncode==0, 'replay failed: '+str(command))
    require(not completed.stderr, 'unexpected replay stderr')
    require(completed.stdout==(root/receipt).read_bytes(), 'receipt replay mismatch: '+receipt)


def main():
    root = Path(__file__).resolve().parent
    count, seal = authenticate(root)
    # NO stored checker or old verifier runs until all bytes, including
    # code, private sources, manifests and receipts, are authenticated.
    replay(root, [sys.executable, '-B', str(root/'checks.py')], 'check-receipt.json')
    replay(root, [sys.executable, '-B', str(root/'inputs/private/frozen-r5/verify.py')],
           'prior-verifier-receipt.json')
    print(json.dumps({'authentication':'PASS', 'files_authenticated':count,
                      'read_only':True, 'both_receipt_replays':'PASS',
                      'seal_sha256':seal, 'full_target_B':'UNRESOLVED',
                      'U_tail':'proved deduction; not independently reviewed',
                      'U_sharp':'UNPAID', 'substantial_complete_result':False},
                     indent=2, sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        print('VERIFICATION FAILED: '+str(error), file=sys.stderr)
        sys.exit(1)
