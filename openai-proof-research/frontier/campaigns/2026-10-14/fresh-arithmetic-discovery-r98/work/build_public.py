#!/usr/bin/env python3
"""Author-side: write public/primary-register.json and public/context-register.json after checking copies."""
import hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PK = ROOT / 'packet'
CAMPAIGN = ROOT.parent
PROJECT = ROOT.parents[3]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


PRIMARY = [
    {'local': 'private/primary/pnas00494-0047.png',
     'citation': 'D. S. Carter, A. Vogt, Collinearity-preserving functions between Desarguesian planes, Proc. Natl. Acad. Sci. USA 77(7) (1980) 3756-3757, page 3756',
     'identifiers': {'doi': '10.1073/pnas.77.7.3756', 'pmc': 'PMC349703'},
     'retrieval': 'PMC scanned page image; exact retrieval URL not retained',
     'read_extent': 'full page (both columns)',
     'used_for': 'definitions (lineation, full/reduced/collapsed, place, prevaluation group), Extension Theorem'},
    {'local': 'private/primary/pnas00494-0048.png',
     'citation': 'D. S. Carter, A. Vogt, Collinearity-preserving functions between Desarguesian planes, Proc. Natl. Acad. Sci. USA 77(7) (1980) 3756-3757, page 3757',
     'identifiers': {'doi': '10.1073/pnas.77.7.3756', 'pmc': 'PMC349703'},
     'retrieval': 'PMC scanned page image; exact retrieval URL not retained',
     'read_extent': 'full page (both columns)',
     'used_for': 'five canonical types, Characterization Theorem (announced; proofs deferred to Mem. AMS 235)'},
    {'local': 'private/primary/machala-CasPestMat_100-1975-2_6.pdf',
     'citation': 'F. Machala, Homomorphismen von projektiven Raeumen und verallgemeinerte semilineare Abbildungen, Casopis pro pestovani matematiky 100 (1975) 142-154',
     'identifiers': {'dml_cz': 'http://dml.cz/dmlcz/108761'},
     'retrieval': 'DML-CZ PDF; exact bitstream URL not retained; persistent URL from the PDF cover page',
     'read_extent': 'full (text extraction)',
     'used_for': 'Definition 2, Definition 3, Theorem (p.145): Step 1 of Theorem D'},
    {'local': 'private/primary/havlicek-arXiv-1210.2053v1.pdf',
     'citation': 'H. Havlicek, Weak linear mappings - a survey, arXiv:1210.2053v1',
     'identifiers': {'arxiv': '1210.2053v1'},
     'retrieval': 'arXiv PDF; exact retrieval URL not retained',
     'read_extent': 'full (text extraction)',
     'used_for': 'navigation to Rado, Machala, Brezuleanu-Radulescu'},
]

HISTORY = [
    ('private/history/fresh-arithmetic-r98-brief.txt', 'expanded-target-2026-10-17/fresh-arithmetic-r98-brief.txt'),
    ('private/history/research-brief-2026-10-20.txt', 'expanded-target-2026-10-17/research-brief-2026-10-20.txt'),
    ('private/history/r97-REPORT.md', 'fresh-arithmetic-discovery-r97/REPORT.md'),
    ('private/history/r97-public-report.md', 'fresh-arithmetic-discovery-r97/packet/public/report.md'),
    ('private/history/r97-screens.md', 'fresh-arithmetic-discovery-r97/packet/public/screens.md'),
    ('private/history/r97-reading-limits.md', 'fresh-arithmetic-discovery-r97/packet/public/reading-limits.md'),
    ('private/history/r97-parent-intake.json', 'discovery-arithmetic-r97-parent/intake.json'),
]


def main():
    prim = []
    for x in PRIMARY:
        p = PK / x['local']
        prim.append(dict(x, sha256=sha(p), size=p.stat().st_size))
    have = {q.relative_to(PK).as_posix() for q in (PK / 'private/primary').iterdir()}
    assert have == {x['local'] for x in prim}, have
    (PK / 'public/primary-register.json').write_text(json.dumps(prim, indent=1) + '\n')

    copies = []
    for local, origin in HISTORY:
        a, b = PK / local, CAMPAIGN / origin
        assert a.read_bytes() == b.read_bytes(), local
        copies.append({'local': local, 'origin': 'frontier/campaigns/2026-10-14/' + origin, 'read_extent': 'full',
                       'sha256': sha(a), 'size': a.stat().st_size})
    have = {q.relative_to(PK).as_posix() for q in (PK / 'private/history').iterdir()}
    assert have == {c['local'] for c in copies}, have
    (PK / 'public/context-register.json').write_text(json.dumps({'copies': copies}, indent=2) + '\n')
    print(len(prim), len(copies))


if __name__ == '__main__':
    main()
