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
    require(all(isinstance(value,dict) and isinstance(value.get('sha256'),str) and len(value['sha256'])==64 for value in EXPECTED_ANCHORS.values()), 'independent review anchors not yet adopted')
    require(gate.get('anchors') == EXPECTED_ANCHORS, 'gate dependency anchors changed')
    require(gate.get('artifacts') == EXPECTED_REVIEW_ARTIFACTS, 'final review artifact selection changed')
    require(gate.get('parent_adoption') == EXPECTED_ADOPTION, 'parent adoption binding changed')


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
EXPECTED_ANCHORS = {'fresh-arithmetic-discovery-r38': {'file': 'manifest.json', 'sha256': '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9'}, 't205m-proof-r1': {'file': 'manifest.json', 'sha256': '4b41e5dd7cd63401630fade2451fae8a341b0f21f62e5b92a96561aa89674343'}, 't205m-contribution-r1': {'file': 'manifest.json', 'sha256': 'e70b5707f7787dbeaa155f4540d51358d5db8fcb4f4850c15c9328735baa526a'}, 't205m-formal-v1': {'file': 'manifest.json', 'sha256': '3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2'}, 't205m-formal-review-r1': {'file': 'review-manifest.json', 'sha256': '5824a6bd5b1fa6c87774b7d0e496f0cda8fe80005c00a98a51987c701cea4ea7'}, 't205m-manuscript-v1': {'file': 'manifest.json', 'sha256': '88bf34ebfd3a0dd4d98a2c3bb1da76820bd30b5b17e2fecb8d5f5248bd782f26'}, 't205m-manuscript-review-r1': {'file': 'review-manifest.json', 'sha256': '919e31c10747db7a7328327179ea5c3ef3c00f482e9e61643a451b9f173a38d2'}}
EXPECTED_PARENT_RECORDS = {'frontier/campaigns/2026-10-14/t205m-parent/contribution-credit-addendum.md': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/contribution-credit-addendum.md', 'bytes': 2968, 'sha256': 'c8c13a9391cad53435b7a9f244746366519dbd2dd76c49845a628a9b3a38b616'}, 'frontier/campaigns/2026-10-14/t205m-parent/contribution-gate-disposition.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/contribution-gate-disposition.json', 'bytes': 1441, 'sha256': '41e9e731af3e59f99892c22212d028e7c00c4e31360ad56ff0784096d94cc47c'}, 'frontier/campaigns/2026-10-14/t205m-parent/formal-gate-disposition.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/formal-gate-disposition.json', 'bytes': 1185, 'sha256': '69ff00e95e9f5279d2b86677748dd335922aaf6b472a286604615acddd1e48a1'}, 'frontier/campaigns/2026-10-14/t205m-parent/manuscript-review-r1-adoption.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/manuscript-review-r1-adoption.json', 'bytes': 8943, 'sha256': 'efd9e4dce61c55e974a19d9a05e2d8e63618286dc90a2226cad0e4740627bbdb'}, 'frontier/campaigns/2026-10-14/t205m-parent/proof-gate-disposition.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/proof-gate-disposition.json', 'bytes': 478, 'sha256': 'ceb004a49e2bc863038f3d8a27207d803cd5479561cf17a4446d40f63f396587'}, 'frontier/campaigns/2026-10-14/t205m-parent/selected-formal-portability.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/selected-formal-portability.json', 'bytes': 6251, 'sha256': 'b259ad0dcb5285ca810066201d1b54722d9f83297da6503341cd84e7d83552b3'}, 'frontier/campaigns/2026-10-14/t205m-parent/source-precheck.json': {'path': 'frontier/campaigns/2026-10-14/t205m-parent/source-precheck.json', 'bytes': 6958, 'sha256': 'f9a7d30974fb736dce3c212f5b983c77df319be3f65fee9ff078d5211ec85eab'}}
EXPECTED_REVIEW_ARTIFACTS = [{'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/review.md', 'bytes': 17801, 'sha256': '06ab577b9851c5f7035c15f911fd92dc0513f4edd59a40104d5c9b6ea60079dc'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/reading-limits.md', 'bytes': 2792, 'sha256': '4da3f6e1c69a8b74ec5e4f670177aeb97bcfde1f3fd1be38ee120aae2e5f805a'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/review-manifest.json', 'bytes': 3533, 'sha256': '919e31c10747db7a7328327179ea5c3ef3c00f482e9e61643a451b9f173a38d2'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/independent_finite.py', 'bytes': 14695, 'sha256': '1504e3a3d7629d22a2a301a96187512d0715052917eed2a8feab538776c7f3d8'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/independent-finite-out.json', 'bytes': 2687, 'sha256': '2eb1a60ea616a220584f55502ab95481dffb15e53c2d8cf0262174860383dc07'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/lemma_controls.py', 'bytes': 5723, 'sha256': '8f3530b5458e4c419dbd049b17c4505b36940db5be78cd22657f52b4cc4aae15'}, {'path': 'frontier/campaigns/2026-10-14/t205m-manuscript-review-r1/lemma-controls-out.json', 'bytes': 1320, 'sha256': '9f5db756afd829c16aa2110fe3b99e91f72db3eee379334a1fc01d5d7879b907'}]
EXPECTED_ADOPTION = {'path': 'frontier/campaigns/2026-10-14/t205m-parent/manuscript-review-r1-adoption.json', 'bytes': 8943, 'sha256': 'efd9e4dce61c55e974a19d9a05e2d8e63618286dc90a2226cad0e4740627bbdb'}


def public_path(name):
    parts=safe(name).parts
    require(not any(x in ('private','.lake','__pycache__','node_modules','.git','cache') for x in parts),'private/cache payload forbidden')
    require(not name.endswith(('.olean','.ilean','.o','.so','.pyc')),'compiled/cache payload forbidden')


def verify_inputs(get,selection,gate):
    gate_check(gate)
    prefix='frontier/campaigns/2026-10-14/'
    manifests={}
    for packet,entry in EXPECTED_ANCHORS.items():
        raw=get(prefix+packet+'/'+entry['file'])
        require(sha(raw)==entry['sha256'],'external packet anchor mismatch: '+packet)
        manifests[packet]=parse(raw)
    seen=set()
    for row in selection['files']+gate['artifacts']:
        name=row['path'];public_path(name);require(name not in seen,'duplicate selected path');seen.add(name)
        require(name.startswith(prefix),'selection outside campaign');packet,rel=name[len(prefix):].split('/',1)
        check(get(name),row)
        if packet in manifests:
            if rel==EXPECTED_ANCHORS[packet]['file']:continue
            files=manifests[packet]['files'];entry=files[rel] if isinstance(files,dict) else next(x for x in files if x['path']==rel)
            require(entry['sha256']==row['sha256'] and entry.get('bytes',entry.get('size'))==row['bytes'],'selected file not bound by frozen packet: '+name)
        else:require(EXPECTED_PARENT_RECORDS.get(name)==row,'unbound parent record')
    for packet,entry in EXPECTED_ANCHORS.items():require(prefix+packet+'/'+entry['file'] in seen,'missing selected anchor')
    require(set(EXPECTED_PARENT_RECORDS)<=seen,'missing parent evidence')
    adoption=parse(get(EXPECTED_ADOPTION['path']))
    require(adoption['status']=='ADOPTED_PASS_FULL_MANUSCRIPT_T205M' and adoption['review_manifest_sha256']==EXPECTED_ANCHORS['t205m-manuscript-review-r1']['sha256'],'parent adoption content changed')
    return len(seen)
