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
    expected = {'proof': 'PASS_FULL_RCS128',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_FULL_MANUSCRIPT_RCS128'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_RCS128_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137', 'candidate changed')
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

EXPECTED_ANCHORS = {
 'fresh-structural-discovery-r37': {'file':'MANIFEST.json','sha256':'a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6'},
 'rcs128-proof-r1': {'file':'MANIFEST.json','sha256':'50bf7355f464b4b043d62cdc1ade59d6f268d2d2ccc87f6125ba8b6992dc1a52'},
 'rcs128-contribution-r3': {'file':'manifest.json','sha256':'1d9aba05838e54865579fa1215c6c03f92ebbeef712beacc8a01b557176d11ce'},
 'rcs128-formal-v1': {'file':'manifest.json','sha256':'c3a051864862ebf53c24fce85da991f2e1da18340d38afdae238f3a160361963'},
 'rcs128-formal-review-r2': {'file':'manifest.json','sha256':'776eb20b725cd9fdfcef97fdef16492c2ddc8114da50f2203a7eb6c38bd6ed2e'},
 'rcs128-manuscript-r1': None,
 'rcs128-manuscript-review-r1': None,
}
