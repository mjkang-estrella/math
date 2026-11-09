#!/usr/bin/env python3
"""Write SOURCE-COPIES.json, DOSSIER-MANIFEST.json and stacksort-full-dossier.zip, then verify the ZIP.

Run from the lane root:  python3 -I scripts/package.py
Excluded from the ZIP: tmp/ (lane-local renderer bundle and scratch; hash-bound separately),
the ZIP itself, DELIVERY.json, hashes/*-after*, and logs/package.* (written while packaging).
"""
import hashlib, json, time, zipfile
from pathlib import Path, PurePosixPath

LANE = Path(__file__).resolve().parent.parent
CAMP = LANE.parent
ZIPNAME = 'stacksort-full-dossier.zip'
INNER = 'lean/stacksort-source6.zip'
INNER_SHA = '9b734e2fe521651fd33bbf92bdf05f1b542a6aeb82f90d2cd1e13399d6cf5c2f'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def copies():
    pairs = [('stacksort-formal-r6/stacksort-source6.zip', INNER),
             ('expanded-corpus-r133/raw/345545.jsonl', 'raw/345545.jsonl'),
             ('expanded-corpus-r133/outputs/stack_pairs_P_1_82.json', 'data/stack_pairs_P_1_82.json'),
             ('stacksort-root-ruling-r1.json', 'evidence/stacksort-root-ruling-r1.json'),
             ('expanded-corpus-r133/candidate-345545/CANDIDATE.md', 'evidence/discovery-r133/CANDIDATE.md')]
    for f in ['SUMMARY.md', 'results.json', 'STATEMENT-CORRESPONDENCE.md', 'PROOF.md', 'REPRODUCE.md']:
        pairs.append((f'stacksort-formal-r6/{f}', f'evidence/formal-r6/{f}'))
    for f in ['fresh-build-StackSortFinal6.log', 'direct-literal-five-rerun.log', 'direct-literal-five-kernel.log',
              'direct-literal-six.log', 'regression6-rerun.log']:
        pairs.append((f'stacksort-formal-r6/logs/{f}', f'evidence/formal-r6/{f}'))
    for r in ['r1', 'r2a', 'r2b', 'r3', 'r4', 'r5a', 'r5b']:
        for f in ['SUMMARY.md', 'PROOF.md', 'results.json']:
            pairs.append((f'stacksort-formal-{r}/{f}', f'evidence/formal-rounds/{r}/{f}'))
    for f in ['REVIEW.md', 'review.json', 'outputs/reviewer_P_1_82_and_certificates.json']:
        pairs.append((f'stacksort-review-r1/{f}', f'evidence/review-r1/{PurePosixPath(f).name}'))
    for f in ['REVIEW.md', 'review.json']:
        pairs.append((f'stacksort-fidelity-r1/{f}', f'evidence/fidelity-r1/{f}'))
    pairs.append(('stacksort-parent-final-r1/registry-refresh.json', 'evidence/root-parent-final/registry-refresh.json'))
    for base, dst in [('stacksort-review-r1/dl-r1', 'sources/review-dl-r1'),
                      ('expanded-corpus-r133/downloads/2002.07144v4', 'sources/r133-downloads/2002.07144v4'),
                      ('expanded-corpus-r133/downloads/2004.11367', 'sources/r133-downloads/2004.11367')]:
        for p in sorted((LANE / dst).rglob('*')):
            if p.is_file():
                rel = p.relative_to(LANE / dst)
                pairs.append((f'{base}/{rel}', f'{dst}/{rel}'))
    out = []
    for src, dst in pairs:
        a, b = sha(CAMP / src), sha(LANE / dst)
        out.append({'source': f'../{src}', 'copy': dst, 'source_sha256': a, 'copy_sha256': b, 'identical': a == b})
    rec = {'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'count': len(out),
           'all_identical': all(o['identical'] for o in out), 'copies': out,
           'receipts': 'each fetched source directory carries receipt.json (URL, UTC, status, bytes, sha256) from the fetching lane; sources/review-dl-r1/receipts.jsonl is the review lane fetch log'}
    (LANE / 'SOURCE-COPIES.json').write_text(json.dumps(rec, indent=1) + '\n')
    return rec


def included(rel):
    top = rel.parts[0]
    if top in ('tmp',) or rel.name == ZIPNAME or rel.as_posix() == 'DELIVERY.json':
        return False
    if top == 'hashes' and 'after' in rel.name:
        return False
    if top == 'logs' and rel.name.startswith('package.'):
        return False
    return True


def main():
    cp = copies()
    files = sorted(p for p in LANE.rglob('*') if p.is_file() and included(p.relative_to(LANE)))
    man = {'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'zip': ZIPNAME, 'file_count': len(files) + 1,
           'note': 'DOSSIER-MANIFEST.json itself is in the ZIP; its own hash is recorded in DELIVERY.json',
           'excluded': ['tmp/ (renderer bundle and scratch; see hashes/renderer-inputs.sha256)', ZIPNAME, 'DELIVERY.json',
                        'hashes/*after*', 'logs/package.*'],
           'files': [{'path': p.relative_to(LANE).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in files]}
    (LANE / 'DOSSIER-MANIFEST.json').write_text(json.dumps(man, indent=1) + '\n')
    files.append(LANE / 'DOSSIER-MANIFEST.json')
    zp = LANE / ZIPNAME
    with zipfile.ZipFile(zp, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in files:
            rel = 'stacksort-manuscript-r1/' + p.relative_to(LANE).as_posix()
            zi = zipfile.ZipInfo(rel, date_time=(2026, 11, 3, 0, 0, 0))
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_STORED if p.suffix in ('.zip', '.png', '.pdf') else zipfile.ZIP_DEFLATED
            z.writestr(zi, p.read_bytes())
    want = {f['path']: f['sha256'] for f in man['files']}
    want['DOSSIER-MANIFEST.json'] = sha(LANE / 'DOSSIER-MANIFEST.json')
    bad, inner = [], None
    with zipfile.ZipFile(zp) as z:
        assert z.testzip() is None
        names = z.namelist()
        for n in names:
            assert n.startswith('stacksort-manuscript-r1/') and '..' not in n and not n.startswith('/')
            rel = n.split('/', 1)[1]
            h = hashlib.sha256(z.read(n)).hexdigest()
            if want.get(rel) != h:
                bad.append(rel)
            if rel == INNER:
                inner = h
    ver = {'zip_sha256': sha(zp), 'zip_bytes': zp.stat().st_size, 'members': len(names), 'expected_members': len(want),
           'member_hash_mismatches': bad, 'inner_source_zip_sha256': inner, 'inner_byte_identical': inner == INNER_SHA,
           'source_copies_all_identical': cp['all_identical'], 'source_copies': cp['count'],
           'manifest_sha256': want['DOSSIER-MANIFEST.json']}
    ver['PASS'] = not bad and len(names) == len(want) and ver['inner_byte_identical'] and cp['all_identical']
    (LANE / 'tmp' / 'package-verification.json').write_text(json.dumps(ver, indent=1) + '\n')
    print(json.dumps(ver, indent=1))


if __name__ == '__main__':
    main()
