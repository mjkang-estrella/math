#!/usr/bin/env python3
"""Read-only full-corpus integrity/search reconstruction. Standard library only."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i38_inequality_stability_discovery'
CORPUS = ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
MANIFEST = CORPUS.parent/'corpus-manifest.json'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def audit_corpus():
    source = json.loads(MANIFEST.read_text())
    tree = json.loads((S/'frozen/sources/preprints-tree.json').read_text())
    assert not tree['truncated']
    blobs = {x['path']:x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    expected = json.loads((S/'corpus-screen.json').read_text())
    pats = {k:re.compile(v,re.I) for k,v in expected['patterns'].items()}
    found = {k:[] for k in pats}
    total = 0
    for f in source['files']:
        data = (CORPUS/f['path']).read_bytes()
        assert len(data) == f['bytes'], f['path']
        assert sha(data) == f['sha256'], f['path']
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob == f['git_blob'] == blobs[f['path']], f['path']
        total += len(data)
        content = re.sub(r'\s+', ' ', data.decode('utf-8',errors='replace'))
        for name,pat in pats.items():
            hits = [{'start':m.start(),'context':content[max(0,m.start()-100):m.end()+150]} for m in pat.finditer(content)]
            if hits:
                found[name].append({'path':f['path'],'matches':hits})
    result = {'tree_entries':len(tree['tree']), 'manuscripts':len({x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')}), 'files':len(source['files']), 'bytes':total, 'patterns':expected['patterns'], 'matches':found}
    assert result == expected, 'Corpus search reconstruction differs from frozen record'
    return {k:v for k,v in result.items() if k not in ['matches','patterns']} | {'matching_files':{k:len(v) for k,v in found.items()}}


def screen_prior_project():
    """Current mechanical search, not a claim of reading all matched documents.

    The returned inventory hashes identify this scan; unrelated live project files
    are not immutable mathematical dependencies of I38.
    """
    suffixes = {'.md','.json','.txt','.tex','.py'}
    excluded_parts = {'corpus','pinned','frozen','inputs','cache','.git','__pycache__'}
    pattern = re.compile(r'propeller|mahler|lieb.{0,8}thirring|hanner',re.I)
    inventory, hits, skipped = [], [], []
    for p in sorted(ROOT.rglob('*')):
        if not p.is_file() or p.suffix not in suffixes:
            continue
        rel = p.relative_to(ROOT)
        if excluded_parts.intersection(rel.parts) or 'i38_inequality_stability_discovery' in str(rel) or 'i38-inequality-stability-discovery' in str(rel) or str(rel) == 'sources/preprints-tree.json':
            continue
        if p.stat().st_size > 10_000_000:
            skipped.append(str(rel)); continue
        data = p.read_bytes()
        inventory.append({'path':str(rel),'sha256':sha(data),'bytes':len(data)})
        for n,line in enumerate(data.decode('utf-8',errors='replace').splitlines(),1):
            if pattern.search(line):
                hits.append({'path':str(rel),'line':n,'text':line[:2000]})
    return {'scope':'Current mechanical project search; the inventory is a historical snapshot, not an immutable proof dependency.', 'pattern':pattern.pattern,'extensions':sorted(suffixes),'excluded_path_components':sorted(excluded_parts),'other_exclusions':['owned I38 report and directories','sources/preprints-tree.json','files above 10000000 bytes'], 'large_files_skipped':skipped,'files_scanned':len(inventory),'inventory':inventory,'matches':hits}


if __name__ == '__main__':
    print(json.dumps(audit_corpus(),indent=2))
