#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Small shared integrity routines; hashes establish identity, not mathematics."""
import hashlib
import json
from pathlib import PurePosixPath
import stat


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pairs(values):
    result = {}
    for key, value in values:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=pairs)


def safe(name):
    require(isinstance(name, str), 'non-string path')
    p = PurePosixPath(name)
    require(bool(name) and name != '.' and name == p.as_posix() and not p.is_absolute()
            and '..' not in p.parts and '\\' not in name and ':' not in name,
            'unsafe path: ' + repr(name))
    return p


def read(base, name):
    p = base
    for part in safe(name).parts:
        p = p / part
        require(not p.is_symlink(), 'symlink: ' + name)
    require(stat.S_ISREG(p.lstat().st_mode), 'nonregular/missing file: ' + name)
    require(p.lstat().st_nlink == 1, 'hardlinked file: ' + name)
    return p.read_bytes()


def check(data, row):
    require(len(data) == row['bytes'] and sha(data) == row['sha256'],
            'size/hash mismatch: ' + row['path'])


def gate_check(gate):
    require(gate.get('status') == 'ALL_REVIEW_GATES_PASS', 'final independent gate still pending')
    expected = {'proof': 'PASS_FULL_T027O',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_FORMAL_SUPPORT', 'manuscript': 'PASS_FULL_MANUSCRIPT_T027O'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_T027O_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '0f53abf319dfde7e8e1e88be77f98a5e0c423dcb0f9ffd99993088dc59b5cda2', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'e5812790dc336e2184ffbee58882fb154175554b9e23e0cacedeecac6bf48867', 'candidate changed')
    require(gate.get('accepted') is False and gate.get('published') is False and gate.get('count_change') == 0, 'preparation boundary changed')
    require(all(value is not None for value in EXPECTED_ANCHORS.values()), 'independent review anchors not yet adopted')
    require(gate.get('anchors') == EXPECTED_ANCHORS, 'gate dependency anchors changed')


def bound_anchors(get, gate):
    for name, entry in gate['anchors'].items():
        path='frontier/campaigns/2026-10-14/'+name+'/'+entry['file']
        require(sha(get(path))==entry['sha256'], 'frozen anchor bytes changed: '+path)


def directory_set(names):
    result=set()
    for name in names:
        p=safe(name)
        result.update(str(q) for q in p.parents if str(q)!='.')
    return result

EXPECTED_ANCHORS = {'fresh-arithmetic-discovery-r36': {'file': 'manifest.json', 'sha256': '2127e23fd2698f75585c70ec4be93d599bb449c8d0f20a4bf6013a00cd7f0199'}, 't027o-proof-r1': {'file': 'manifest.json', 'sha256': '880af01c42e07f0a22a7f762f2e372065fc5a2cbcd82dea8f1f212203e5d8fa9'}, 't027o-contribution-r1': {'file': 'manifest.json', 'sha256': 'e8bbf2c96ff1946514d1f7fe4e7123f3800a99b9ef623120d4f1cea2dfcc30cc'}, 't027o-formal-v1': {'file': 'manifest.json', 'sha256': 'b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4'}, 't027o-formal-review-r1': {'file': 'review-manifest.json', 'sha256': '2d71cfd5193c76f59c8b3bc5aa3e2fa9a5dea3191badfc6a868aa859d5789f2a'}, 't027o-manuscript-v1': {'file': 'manifest.json', 'sha256': '2c9715e9a6825726d3bc630b31e7ecf214071e4878cf74d0706b1bc8c63da3dc'}, 't027o-manuscript-review-r1': None}
