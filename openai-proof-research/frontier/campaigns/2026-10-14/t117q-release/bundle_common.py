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
    expected = {'proof': 'PASS_FULL_T117Q',
                'contribution': 'SUBSTANTIAL',
                'formal': 'PASS_SCOPED_T117Q', 'manuscript': 'PASS_FULL_MANUSCRIPT_T117Q'}
    require(gate.get('verdicts') == expected, 'required verdicts missing or different')
    require(gate.get('full_claim_unchanged') is True, 'scope not bound')
    require(gate.get('full_T117Q_formalized') is False, 'unsupported full formal claim')
    require(gate.get('artifacts'), 'no actual final review artifacts')

    require(gate.get('source_pin') == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin changed')
    require(gate.get('scope_sha256') == 'fc5a8f872843cd4c0448c6fb6ba4864cf17044f6ab7366d3010ca551ebdbfe36', 'frozen scope changed')
    require(gate.get('candidate_sha256') == 'e32f7a12592e237b5bb428aa7cb0f9f29d01739b6c3230ceb2fcca15129aeea4', 'candidate changed')
    require(gate.get('accepted') is False and gate.get('published') is False and gate.get('count_change') == 0, 'preparation boundary changed')
    require(all(isinstance(value, dict) and isinstance(value.get('sha256'), str) and len(value['sha256']) == 64 and all(c in '0123456789abcdef' for c in value['sha256']) for value in EXPECTED_ANCHORS.values()), 'independent review anchors not yet adopted')
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
EXPECTED_ANCHORS = {'fresh-structural-discovery-r59': {'file': 'MANIFEST.json', 'sha256': '053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2'}, 't117q-proof-r1': {'file': 'MANIFEST.json', 'sha256': 'bb6941a24d155f8fb0e6fc36656b3b73cda7946fbd6047558005a612665a3cea'}, 't117q-contribution-r1': {'file': 'MANIFEST.json', 'sha256': '6d6366df9904a9d49db95e218c1daf52b444878ee2ec9ecf6938f9b84dfb5013'}, 't117q-parent-literature-r1': {'file': 'manifest.json', 'sha256': 'c93929fee2e269bb07015e91254aa8865a57a45a2b9879068da8f52ea0f9deb8'}, 't117q-contribution-r2': {'file': 'MANIFEST.json', 'sha256': '855f772948a48f556d6680b8cfe991ea0d3b1d539c190fafcc89e4920fc8c4c0'}, 't117q-formal-v1': {'file': 'manifest.json', 'sha256': 'b741e2d76e9383238b5f3e975c634e2bb48b75eaa00dc1fb93371b0a1c139b37'}, 't117q-formal-review-r1': {'file': 'review-manifest.json', 'sha256': '98fde2d10f3b410238e294df07a300f2bdd2f9d641844d0d4066b828f1449ae4'}, 't117q-manuscript-v1': {'file': 'manifest.json', 'sha256': '1a127b603f1f44ff0ae0fb7ea55736ac4f849d888768f97614684d29a094e982'}, 't117q-manuscript-review-r1': None}


def public_path(name):
    parts=safe(name).parts
    require(not any(part in ('private','.lake','__pycache__','node_modules','.git','cache') for part in parts), 'private/cache payload forbidden')
    require(not name.endswith(('.olean','.ilean','.o','.so','.pyc')), 'compiled/cache payload forbidden')
