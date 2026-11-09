#!/usr/bin/env python3
"""Build source and context registers for the r97 packet (author-side, run before sealing)."""
import hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'packet'
PROJECT = ROOT.parents[3]
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_PATH = PROJECT / 'sources/preprints-tree.json'
CAMP = 'frontier/campaigns/2026-10-14/'

HISTORY = [
    ('research-brief-2026-10-20.txt', CAMP + 'expanded-target-2026-10-17/research-brief-2026-10-20.txt', 'full'),
    ('fresh-arithmetic-r97-brief.txt', CAMP + 'expanded-target-2026-10-17/fresh-arithmetic-r97-brief.txt', 'full'),
    ('r96-REPORT.md', CAMP + 'fresh-arithmetic-discovery-r96/REPORT.md', 'full'),
    ('r96-public-report.md', CAMP + 'fresh-arithmetic-discovery-r96/packet/public/report.md', 'full'),
    ('r96-screens.md', CAMP + 'fresh-arithmetic-discovery-r96/packet/public/screens.md', 'full'),
    ('r96-reading-limits.md', CAMP + 'fresh-arithmetic-discovery-r96/packet/public/reading-limits.md', 'full'),
    ('r96-parent-intake.json', CAMP + 'discovery-arithmetic-r96-parent/intake.json', 'full'),
    ('r24-screen-009.md', CAMP + 'fresh-arithmetic-discovery-r24/payload/screen-009.md', 'full'),
    ('r73-reading-and-credit.md', CAMP + 'fresh-arithmetic-discovery-r73/reading-and-credit.md', 'lines 15-30'),
]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    tree_bytes = TREE_PATH.read_bytes()
    tree = json.loads(tree_bytes)['tree']
    by_path = {e['path']: e for e in tree}
    retained = []
    for p in sorted((PACKET / 'private/upstream').rglob('*')):
        if not p.is_file():
            continue
        rel = p.relative_to(PACKET / 'private/upstream').as_posix()
        b = p.read_bytes()
        e = by_path[rel]
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['sha'] and len(b) == e['size'], rel
        retained.append({'family': '009', 'upstream_path': rel, 'local': 'private/upstream/' + rel,
                         'raw_url': 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + rel,
                         'git_blob': blob, 'size': len(b), 'sha256': sha(b), 'status': 'read in full'})
    reg = {'pin': PIN, 'tree_sha256': sha(tree_bytes), 'tree_entries': len(tree), 'truncated': False,
           'retained': retained, 'removed': []}
    (PACKET / 'public/source-register.json').write_text(json.dumps(reg, indent=2, sort_keys=True) + '\n')
    copies = []
    for local, origin, extent in HISTORY:
        o = (PROJECT / origin).read_bytes()
        c = (PACKET / 'private/history' / local).read_bytes()
        assert o == c, local
        copies.append({'local': 'private/history/' + local, 'origin': origin, 'read_extent': extent,
                       'sha256': sha(c), 'size': len(c)})
    (PACKET / 'public/context-register.json').write_text(json.dumps({'copies': copies}, indent=2, sort_keys=True) + '\n')
    (PACKET / 'public/primary-register.json').write_text('[]\n')
    print(len(retained), 'sources;', len(copies), 'history copies')


if __name__ == '__main__':
    main()
