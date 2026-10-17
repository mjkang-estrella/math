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
    expected = {'proof': 'PASS_FULL_AGM063',
                'contribution': 'SUBSTANTIAL_MODERATE',
                'formal': 'PASS_SCOPED_SUPPORT', 'manuscript': 'PASS_FULL_MANUSCRIPT_AGM063'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_AGM063_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == '03a4861c0ebd9ae1951bc3650d17d004f53e46303f3074425bb7e19d05677081', 'frozen scope changed')
    require(gate.get('candidate_sha256') == '285f584005acf9c5ed3fbaf9c6bd3ef320eecaf88df21ca22bace3ee7d971c8c', 'candidate changed')
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
 'fresh-arithmetic-discovery-r18': {'file':'manifest.json','sha256':'9afeca9bf3d6c272d7013e48c62e53ae92b1b1d4ccd3f52adcd9f35375cbb786'},
 'agm063-proof-r1': {'file':'review-manifest.json','sha256':'daf2c9f1e9e7878971e4568c3088107d911c79b3e93d72ad9368466cc4df9312'},
 'agm063-contribution-r1': {'file':'manifest.json','sha256':'7f9621436850a9415e1dcd55f1ff869b7bf9e3f216add131ba6d0bf432278891'},
 'agm063-formal-v1': {'file':'output-manifest.json','sha256':'ca6bdb0cccd691d0c8a94ff8ec3bfbd9ccdd87a64ba5b4cf344a1b1c73b8ad9c'},
 'agm063-formal-review-r1': {'file':'review-manifest.json','sha256':'d1b788176d9f9d7759d99fb874a6ccea6ad9233faf5d3c01d00bdc8a1d6863fb'},
 'agm063-manuscript-r1': {'file':'output-manifest.json','sha256':'5a043ad5acdf541b9a10d912dbd0339b3c8c0aa2650bd92a4a41d5422d0c34bb'},
 'agm063-manuscript-review-r1': None,
}
