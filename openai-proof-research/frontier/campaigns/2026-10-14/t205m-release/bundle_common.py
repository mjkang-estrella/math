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
    require(not base.is_symlink() and not any(p.is_symlink() for p in base.parents), 'symlink root ancestry')
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
    expected = {'proof': 'PASS_FULL_T205M',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_T205M', 'manuscript': 'PASS_FULL_MANUSCRIPT_T205M'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_T205M_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '3eb9d790999b419a4083ead2a3ed0979217a36a12bdd78ceabe7fa6d3afb64f6', 'frozen scope changed')
    require(gate.get('candidate_sha256') == '17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5', 'candidate changed')
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

# Parent must adopt the actual independent manuscript review before replacing None.
EXPECTED_ANCHORS = {'fresh-arithmetic-discovery-r38': {'file': 'manifest.json', 'sha256': '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9'}, 't205m-proof-r1': {'file': 'manifest.json', 'sha256': '4b41e5dd7cd63401630fade2451fae8a341b0f21f62e5b92a96561aa89674343'}, 't205m-contribution-r1': {'file': 'manifest.json', 'sha256': 'e70b5707f7787dbeaa155f4540d51358d5db8fcb4f4850c15c9328735baa526a'}, 't205m-formal-v1': {'file': 'manifest.json', 'sha256': '3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2'}, 't205m-formal-review-r1': {'file': 'review-manifest.json', 'sha256': '5824a6bd5b1fa6c87774b7d0e496f0cda8fe80005c00a98a51987c701cea4ea7'}, 't205m-manuscript-v1': {'file': 'manifest.json', 'sha256': '88bf34ebfd3a0dd4d98a2c3bb1da76820bd30b5b17e2fecb8d5f5248bd782f26'}, 't205m-manuscript-review-r1': None}
