"""Read-only identity verifier for the T314C contribution review r1.

Requires an externally supplied SHA-256 of this directory's MANIFEST.json and checks it
before trusting any other byte. Then authenticates the author packet against its external
anchors, the copied source314 blobs against the canonical preprint tree, and the frozen
review inputs. A successful run certifies identity/provenance only: not the proof, not the
contribution verdict, not acceptance.
"""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path

AUTHOR_DIR = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r66'
AUTHOR_MANIFEST = 'b8b77b3b52e977ca3abd1ce9167ca605c2dae722f855e7b2ff67c43b5826ff4a'
AUTHOR_CANDIDATE = '7bc61c8a0949c671a5f8dd8b9f55502e1b526ed40968dc0912be984f789eaea9'
AUTHOR_SCOPE = '676eed9172e85a2c99a7ff52dbe911cae036c104dba0bb409a2b158e4791f29e'
TREE_PATH = 'sources/preprints-tree.json'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
TREE_ENTRIES = 13223
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/'


class Reject(Exception):
    pass


def sha(b):
    return hashlib.sha256(b).hexdigest()


def need(ok, reason):
    if not ok:
        raise Reject(reason)


def safe_rel(p):
    q = Path(p)
    return not q.is_absolute() and '..' not in q.parts


def verify(review, repo, expected, private_dir=None, replay=False):
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected) is not None, 'EXPECTED_ANCHOR')
    raw = (review / 'MANIFEST.json').read_bytes()
    need(sha(raw) == expected, 'REVIEW_MANIFEST_ANCHOR')
    m = json.loads(raw)
    entries = list(review.rglob('*'))
    need(not any(x.is_symlink() for x in entries), 'REVIEW_SYMLINK')
    files = {str(x.relative_to(review)) for x in entries if x.is_file()} - {'MANIFEST.json'}
    need(files == set(m['files']), 'REVIEW_FILE_MEMBERSHIP')
    dirs = sorted(str(x.relative_to(review)) for x in entries if x.is_dir())
    need(dirs == m['directories'], 'REVIEW_DIRECTORY_MEMBERSHIP')
    for f, h in m['files'].items():
        need(safe_rel(f), 'UNSAFE_PATH')
        need(sha((review / f).read_bytes()) == h, 'REVIEW_PAYLOAD_HASH')

    # Author packet, external anchors first.
    a = repo / AUTHOR_DIR
    need(sha((a / 'candidate.md').read_bytes()) == AUTHOR_CANDIDATE, 'AUTHOR_CANDIDATE_ANCHOR')
    need(sha((a / 'original-scope.md').read_bytes()) == AUTHOR_SCOPE, 'AUTHOR_SCOPE_ANCHOR')
    araw = (a / 'MANIFEST.json').read_bytes()
    need(sha(araw) == AUTHOR_MANIFEST, 'AUTHOR_MANIFEST_ANCHOR')
    am = json.loads(araw)
    aentries = list(a.rglob('*'))
    need(not any(x.is_symlink() for x in aentries), 'AUTHOR_SYMLINK')
    afiles = {str(x.relative_to(a)) for x in aentries if x.is_file()} - {'MANIFEST.json'}
    need(afiles == set(am['files']), 'AUTHOR_MEMBERSHIP')
    need(sorted(str(x.relative_to(a)) for x in aentries if x.is_dir()) == am['directories'], 'AUTHOR_DIRECTORIES')

    # Canonical tree and the twelve copied source314 text blobs.
    tb = (repo / TREE_PATH).read_bytes()
    need(sha(tb) == TREE_SHA, 'TREE_ANCHOR')
    t = json.loads(tb)
    need(t.get('truncated') is False and len(t['tree']) == TREE_ENTRIES, 'TREE_SHAPE')
    canon = {x['path']: x for x in t['tree']}
    need(len(canon) == TREE_ENTRIES, 'TREE_UNIQUE')
    receipts = json.loads((a / 'source-receipts.json').read_text())
    selected = {x['path'] for x in t['tree'] if x['type'] == 'blob'
                and x['path'].startswith(PREFIX) and not x['path'].endswith('.pdf')}
    need(len(receipts) == 12 and {x['path'] for x in receipts} == selected, 'SOURCE_MEMBERSHIP')
    for x in receipts:
        need(x['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'], 'SOURCE_URL')
        need(safe_rel(x['copy']), 'UNSAFE_PATH')
        b = (a / x['copy']).read_bytes()
        git = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        need(git == canon[x['path']]['sha'], 'SOURCE_GIT')
    for f, h in am['files'].items():
        need(safe_rel(f), 'UNSAFE_PATH')
        need(sha((a / f).read_bytes()) == h, 'AUTHOR_PAYLOAD_HASH')

    # Frozen review inputs (hash-covered list inside this review).
    inp = json.loads((review / 'inputs-manifest.json').read_text())
    for x in inp['frozen']:
        need(safe_rel(x['path']), 'UNSAFE_PATH')
        need(sha((repo / x['path']).read_bytes()) == x['sha256'], 'INPUT_HASH')
    observed = {}
    for x in inp['observed_mutable']:
        p = repo / x['path']
        observed[x['path']] = ('missing' if not p.is_file() else
                               'unchanged' if sha(p.read_bytes()) == x['sha256'] else 'changed-since-review')

    private = 'not checked'
    if private_dir is not None:
        for x in inp['private_external']:
            need(sha((Path(private_dir) / x['file']).read_bytes()) == x['sha256'], 'PRIVATE_HASH')
        private = 'verified'

    replayed = False
    if replay:
        r = subprocess.run([sys.executable, '-B', str(review / 'diagnostics.py')], capture_output=True, text=True)
        need(r.returncode == 0, 'DIAGNOSTIC_REPLAY')
        need(json.loads(r.stdout) == json.loads((review / 'diagnostic-results.json').read_text()), 'DIAGNOSTIC_REPLAY')
        replayed = True

    return {'identity': 'verified', 'review_payloads': len(files), 'author_payloads': len(afiles),
            'source_blobs': 12, 'frozen_inputs': len(inp['frozen']), 'observed_mutable': observed,
            'private_external': private, 'diagnostic_replay': replayed,
            'limits': 'identity/provenance only; no proof, contribution, formal or acceptance certification'}


if __name__ == '__main__':
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected', required=True)
    ap.add_argument('--review', type=Path, default=here)
    ap.add_argument('--repo', type=Path, default=here.parents[3])
    ap.add_argument('--private-dir', type=Path)
    ap.add_argument('--replay', action='store_true')
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.review, a.repo, a.expected, a.private_dir, a.replay), sort_keys=True))
    except (Reject, OSError, KeyError, ValueError) as e:
        print('REJECT: ' + (str(e) if isinstance(e, Reject) else type(e).__name__ + ': ' + str(e)))
        raise SystemExit(1)
