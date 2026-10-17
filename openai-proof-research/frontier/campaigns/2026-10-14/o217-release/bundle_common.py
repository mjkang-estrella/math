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
    expected = {'proof': 'PASS_FULL_O217',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_FULL_MANUSCRIPT_O217'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_O217_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '78fc15d24a91bbc2a8e27f679b78c4e551ef0c25d84214dd5dcc48e14ee99584', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'a2aca38071a48fba5cccad7df731626202c6a8ca778ade57f76759c1d321cf37', 'candidate changed')
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

EXPECTED_ANCHORS = {'fresh-analytic-discovery-r28': {'file': 'output-manifest.json', 'sha256': '1d299a1840795fe279f89aa04fd4ca55cb58d283b3f7ed2fb5001c136d97d48f'}, 'o217-proof-r1': {'file': 'manifest.json', 'sha256': 'd911f12e60858715ffe18a1fba3b3b45f11ab6bf67b54c04884b76b50841c98a'}, 'o217-contribution-r1': {'file': 'review-manifest.json', 'sha256': '3c620966f45054e96bad4389029026d103c6a1b0b51167928ce95a3ca2ace43b'}, 'o217-formal-v1': {'file': 'output-manifest.json', 'sha256': '121cf88cc61d36d24edeb89f011a1fa2d405292ae389d03f91e3f5aee6a568ce'}, 'o217-formal-review-r1': {'file': 'review-manifest.json', 'sha256': '8d17abf38d8c9fac2228dc7f4296a2a73d9c4c0ea4944243b90238fe75c2a1f5'}, 'o217-manuscript-r1': {'file': 'output-manifest.json', 'sha256': 'd698c8aaa65a2c3cce67b5824e15d9ef85c5f5c29ab6a70194faecd8ca9f506b'}, 'o217-manuscript-review-r1': {'file': 'review-manifest.json', 'sha256': '18f4143063696abf44f87d289daef86fe37d84b995fea41c245169ebea159100'}}
