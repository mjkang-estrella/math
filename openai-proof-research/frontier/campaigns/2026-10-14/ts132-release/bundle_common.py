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
    expected = {'proof': 'PASS_FULL_TS132',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_MANUSCRIPT'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_TS132_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'e1e93a97ddae2d47d32feb0fa464da93c32d4de661c93b63ac0e7ff785de310a', 'candidate changed')
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

EXPECTED_ANCHORS = {'fresh-structural-discovery-r27': {'file': 'manifest.json', 'sha256': '2fabba39b9b907f675c01162eae65b970236923ed5b14b611017a515f7eef267'}, 'ts132-proof-r1': {'file': 'manifest.json', 'sha256': '0a4ddaafa1b82d231fa65a9117b4d49a4528483756f65a0ed62374bd3b3152ca'}, 'ts132-contribution-r1': {'file': 'manifest.json', 'sha256': '2ba7365098c5b2a7fb1caa39e5f387d5067cf3e58fa954ff97de15c03b16b764'}, 'ts132-formal-v1': {'file': 'output-manifest.json', 'sha256': '55c87693245c7812a3097667d098c987c2f91bc8b861b16e84bc56eb3a42b93e'}, 'ts132-manuscript-r1': {'file': 'manifest.json', 'sha256': '782cd8770c3cfa3890a05882f09bd6dbf61a3540aa841276d7e035c323e9adbc'}, 'ts132-formal-review-r1': {'file': 'manifest.json', 'sha256': '060f9caddbd94f2517193c00fc0a66eacec5d5ed142ee7e5b5f9fa07d32f971b'}, 'ts132-manuscript-review-r1': {'file': 'manifest.json', 'sha256': 'dbe163b6d86274b7d749526045afc42b65341e34efd3a06e4ab222e4271d7cfa'}}
