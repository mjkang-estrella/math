#!/usr/bin/env python3
"""Assemble packet/ (copies, registers). Run once before sealing."""
import hashlib, json, shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN = ROOT.parent
PROJECT = ROOT.parents[3]
PK = ROOT / 'packet'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
RAW = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)


H164 = 'preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/'
EXTENT = {
    H164 + 'README.md': 'read in full',
    H164 + 'build/main.tex': 'fetched; not read',
    H164 + 'build/references.tex': 'keyword search only',
    H164 + 'build/sections/01_introduction.tex': 'read in full',
    H164 + 'build/sections/02_framework.tex': 'lines 230-319 read; keyword search elsewhere',
}


def extent(path):
    if path in EXTENT:
        return EXTENT[path]
    if 'Catalans' in path:
        if path.endswith(('introduction.tex', 'conclusion.tex')):
            return 'read (screen of family 005)'
        if path.endswith('main.tex'):
            return 'fetched; read status before context compaction not durably recorded'
        return 'fetched; not read semantically'
    if 'Commuting-Division' in path:
        if path.endswith(('paper.tex', '01-introduction.tex')):
            return 'read (screen of family 200)'
        return 'partly read (screen of family 200)'
    return 'partly read (screen of family 200 companion)'


def main():
    # pinned sources
    tree = json.loads((PROJECT / 'sources/preprints-tree.json').read_text())
    entries = {e['path']: e for e in tree['tree']}
    log = [json.loads(l) for l in (ROOT / 'work/fetch-log.jsonl').read_text().splitlines()]
    retained = []
    for x in log:
        src = ROOT / 'private/upstream' / x['path']
        local = 'private/upstream/' + x['path']
        copy(src, PK / local)
        e = entries[x['path']]
        retained.append({'upstream_path': x['path'], 'raw_url': RAW + x['path'], 'git_blob': e['sha'],
                         'size': e['size'], 'sha256': sha(src), 'local': local, 'fetched_utc': x['utc'],
                         'read_extent': extent(x['path'])})
    reg = {'pin': PIN, 'tree_sha256': sha(PROJECT / 'sources/preprints-tree.json'),
           'truncated': tree.get('truncated', False), 'tree_entries': len(entries),
           'retained': retained, 'removed': []}
    (PK / 'public/source-register.json').write_text(json.dumps(reg, indent=1) + '\n')
    copy(ROOT / 'work/fetch-log.jsonl', PK / 'public/fetch-log.jsonl')

    # primaries
    meta = {
        'alweiss-2307.08901v6.pdf': ('R. Alweiss, Monochromatic sums and products over Q (arXiv:2307.08901v6)',
                                     'lines 1-825 of 852 of text extraction (all of sections 1-6)'),
        'bowen-sabok-2210.12290v1.pdf': ('M. Bowen and M. Sabok, Monochromatic products and sums in the rationals (arXiv:2210.12290v1)',
                                         'introduction and section 4.3 (Corollary 1.2 proof)'),
        'alweiss-2211.00766-latest.pdf': ('R. Alweiss, Monochromatic sums and products of polynomials (arXiv:2211.00766, served file v4)',
                                          'introduction (lines 1-90) and lines 250-260'),
        'bergelson-leibman-math9907201v1.pdf': ('V. Bergelson and A. Leibman, Set-polynomials and polynomial extension of the Hales-Jewett theorem, Ann. of Math. 150 (arXiv:math/9907201v1)',
                                                'introduction to 0.18 (lines 1-394), 7.9-7.15, 8.7-8.8'),
        'hunter-2308.10749v1.pdf': ('Z. Hunter, On a method of Alweiss (arXiv:2308.10749v1)',
                                    'sections 1-2.2, Lemma 6.1 sketch (lines 690-730), keyword search'),
        'kousek-2407.03304v1.pdf': ('I. Kousek, Revisiting sums and products in countable and finite fields (arXiv:2407.03304v1)',
                                    'abstract and section 1.1'),
        'hunter-2308.10749-abs.html': ('arXiv abstract page for 2308.10749 (version listing)', 'version listing only'),
        'kousek-2407.03304-abs.html': ('arXiv abstract page for 2407.03304 (version listing)', 'version listing only'),
    }
    acq = {}
    for line in (ROOT / 'work/primary-acquisitions.jsonl').read_text().splitlines():
        x = json.loads(line)
        acq[Path(x['file']).name] = x
    abs_url = {'hunter-2308.10749-abs.html': 'https://arxiv.org/abs/2308.10749',
               'kousek-2407.03304-abs.html': 'https://arxiv.org/abs/2407.03304'}
    primary = []
    for name, (cit, ext) in meta.items():
        src = ROOT / 'private/primary' / name
        local = 'private/primary/' + name
        copy(src, PK / local)
        a = acq.get(name)
        rec = {'local': local, 'citation': cit, 'read_extent': ext, 'sha256': sha(src), 'size': src.stat().st_size}
        if a:
            rec['identifiers'] = {'url': a['url'], 'acquired_utc': a['utc']}
            assert a['sha256'] == rec['sha256'], name
        else:
            rec['identifiers'] = {'url': abs_url[name], 'acquired_utc': 'about 2026-10-20T17:16Z (recorded in the note of the matching PDF acquisition)'}
        primary.append(rec)
    (PK / 'public/primary-register.json').write_text(json.dumps(primary, indent=1) + '\n')

    # history copies
    hist = [
        ('discovery-arithmetic-r98-parent/assessment.md', 'read in full'),
        ('discovery-arithmetic-r98-parent/intake.json', 'read in full'),
        ('fresh-arithmetic-discovery-r98/packet/public/screens.md', 'read in full'),
        ('fresh-arithmetic-discovery-r98/packet/public/reading-limits.md', 'read in full'),
        ('fresh-structural-discovery-r35/mixed164.md', 'read in full'),
        ('fresh-arithmetic-discovery-r94/packet/public/other-screens.md', 'family-164 section read'),
        ('fresh-structural-discovery-r130/packet/public/other-screens.md', 'family-164 line and neighbours read'),
    ]
    copies = []
    for i, (rel, ext) in enumerate(hist, 1):
        src = CAMPAIGN / rel
        local = 'private/history/%02d-%s' % (i, rel.replace('/', '__'))
        copy(src, PK / local)
        copies.append({'original': 'frontier/campaigns/2026-10-14/' + rel, 'local': local, 'sha256': sha(src),
                       'size': src.stat().st_size, 'read_extent': ext})
    (PK / 'public/context-register.json').write_text(json.dumps({'copies': copies}, indent=1) + '\n')

    nav = {'web_searches': [
        'monochromatic finite sums and products fields of positive characteristic Alweiss Hindman conjecture',
        'Hunter "On a method of Alweiss" arXiv 2308.10749 fields characteristic',
        '"x+y" "xy" partition regular "characteristic 2" OR "small characteristic" infinite field monochromatic sums products',
        'Hindman finite sums and products conjecture function field F_p(t) positive characteristic partition regularity 2024 2025',
        '"Revisiting sums and products in countable and finite fields" arXiv',
        'Bowen Sabok "Monochromatic products and sums in the rationals" Forum of Mathematics Pi Corollary 1.2 "In fact, our proof"'],
        'result': 'no characteristic-p FS/FP statement found; search not exhaustive',
        'note': 'search-engine result bodies were not retained'}
    (PK / 'public/external-navigation.json').write_text(json.dumps(nav, indent=1) + '\n')

    copy(ROOT / 'freeze/scope-freeze.md', PK / 'public/scope-freeze.md')
    copy(ROOT / 'notes/prefreeze-feasibility.md', PK / 'public/prefreeze-feasibility.md')
    copy(ROOT / 'work/fetch_pinned.py', PK / 'code/fetch_pinned.py')
    status = {'round': 'fresh-arithmetic-discovery-r99', 'pin': PIN, 'status': 'AUTHOR_PROOF_NOMINEE',
              'frozen_target': 'Theorem F and Corollary G (public/scope-freeze.md)',
              'scope_freeze_sha256': sha(ROOT / 'freeze/scope-freeze.md'),
              'author_proof': 'public/proof.md', 'nominee': 'Theorem F with Corollary G, unchanged frozen scope',
              'family': '164', 'self_gates': None, 'count': None,
              'note': 'no correctness, contribution or acceptance verdict is assigned by the author'}
    (PK / 'public/status.json').write_text(json.dumps(status, indent=1) + '\n')
    print('built', len(retained), 'sources', len(primary), 'primaries', len(copies), 'history copies')


if __name__ == '__main__':
    main()
