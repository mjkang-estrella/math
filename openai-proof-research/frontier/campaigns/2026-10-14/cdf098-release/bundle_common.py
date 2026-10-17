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
    return p.read_bytes()


def check(data, row):
    require(len(data) == row['bytes'] and sha(data) == row['sha256'],
            'size/hash mismatch: ' + row['path'])


def gate_check(gate):
    require(gate.get('status') == 'ALL_REVIEW_GATES_PASS', 'final independent gate still pending')
    expected = {'proof': 'PASS_FULL_CDF098',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_MANUSCRIPT'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_CDF098_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == 'bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5', 'frozen scope changed')
    require(gate.get('candidate_sha256') == '24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a', 'candidate changed')
    require(gate.get('accepted') is False and gate.get('published') is False and gate.get('count_change') == 0, 'preparation boundary changed')
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

EXPECTED_ANCHORS = {'fresh-parent-discovery-r8': {'file': 'manifest.json', 'sha256': 'f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85'}, 'cdf098-proof-r1': {'file': 'manifest.json', 'sha256': '543aba870bfb7237dcd95e2d03fd40e644350b7acbc9aa43cb90c08553a80dda'}, 'cdf098-contribution-r1': {'file': 'manifest.json', 'sha256': '42befbcdc270f6802d47080dfba86ef105dcd9316a237324eb0a4a5355f4c691'}, 'cdf098-formal-v1': {'file': 'output-manifest.json', 'sha256': '510548427d70b08ff90285e1ec90ba71cb29905a5ba674ce37902a6ff789cbef'}, 'cdf098-formal-review-r1': {'file': 'seal.json', 'sha256': '40f3e907710fe0ebcea1307074bcd9ac76e73017565bb0688bde78b0f0b88d29'}, 'cdf098-manuscript-r1': {'file': 'seal.json', 'sha256': '14216c0f3656c05406225a7c5d87f652b8e7ef0d5fb358d3bef480dd5aafd881'}, 'cdf098-manuscript-review-r1': {'file': 'seal.json', 'sha256': 'e8aa5b681abca2fa43e849b0ff05c545018c53a336676e48158221355b6b05d9'}}
