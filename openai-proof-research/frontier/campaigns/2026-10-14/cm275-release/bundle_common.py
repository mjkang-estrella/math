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
    expected = {'proof': 'PASS_FULL_CM275',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_MANUSCRIPT'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_CM275_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '5fe6692d799dd949cfdcd87700a3dd9566acdfa5496080991c0e3d9ccad7fd9f', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'b467f8b7797ed4c49c4de799399cffab0bc22629b61a0b214ddf2401e8289ffd', 'candidate changed')
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

EXPECTED_ANCHORS = {'fresh-analytic-discovery-r26': {'file': 'output-manifest.json', 'sha256': '957291975356455fcb76bffd1af3fbaad1d344921049b9f9bf7d9ecdd09b2299'}, 'cm275-proof-r1': {'file': 'output-manifest.json', 'sha256': 'beb36630630f6319ba266a9dfaf50d3f57ad0fce2bc312b490cd27dbbb582257'}, 'cm275-contribution-r1': {'file': 'output-manifest.json', 'sha256': '7ee0388a2964746bb5ea4a9d55ecb446784281e647d219bbaf1ed291a711928e'}, 'cm275-formal-v1': {'file': 'output-manifest.json', 'sha256': 'c834b31ddf0c9c5665146d4456ee792a876f446341ad00da681cb1981a3c76e6'}, 'cm275-manuscript-r1': {'file': 'manifest.json', 'sha256': 'bdb61d89b0d52cbfd4dbc2a68272235958560e28677aeb3029488c8895388e61'}, 'cm275-formal-review-r1': None, 'cm275-manuscript-review-r1': None}
