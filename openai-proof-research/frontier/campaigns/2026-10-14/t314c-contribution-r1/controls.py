"""Negative controls for verify_review.py, run on copies under /var/tmp.

Each control mutates a copied mini-repository and requires the verifier to exit nonzero with
one specific rejection reason. The real tree is never modified. Requires the external review
anchor; the unmodified copy must verify first, so controls are not vacuous.
"""
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
REL = HERE.relative_to(REPO)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def seal(review):
    m = {'status': 'independent contribution review r1; identity seal only',
         'files': {str(x.relative_to(review)): sha(x.read_bytes())
                   for x in sorted(review.rglob('*')) if x.is_file() and x.name != 'MANIFEST.json'},
         'directories': sorted(str(x.relative_to(review)) for x in review.rglob('*') if x.is_dir())}
    (review / 'MANIFEST.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
    return sha((review / 'MANIFEST.json').read_bytes())


def mini_repo(dst):
    inp = json.loads((HERE / 'inputs-manifest.json').read_text())
    paths = [x['path'] for x in inp['frozen']] + ['sources/preprints-tree.json']
    for p in paths:
        (dst / p).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPO / p, dst / p)
    a = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r66'
    shutil.copytree(REPO / a, dst / a, symlinks=True)
    shutil.copytree(HERE, dst / REL, symlinks=True,
                    ignore=shutil.ignore_patterns('__pycache__'))
    return inp


def run(repo, anchor, private=None, replay=False):
    cmd = [sys.executable, '-B', str(repo / REL / 'verify_review.py'), '--expected', anchor,
           '--review', str(repo / REL), '--repo', str(repo)]
    if private:
        cmd += ['--private-dir', str(private)]
    if replay:
        cmd.append('--replay')
    return subprocess.run(cmd, capture_output=True, text=True)


def main(expected, private_dir, replay):
    results = []
    with tempfile.TemporaryDirectory(prefix='t314c-review-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        ok = base / 'baseline'
        mini_repo(ok)
        r = run(ok, expected, private_dir)
        assert r.returncode == 0 and json.loads(r.stdout)['identity'] == 'verified', (r.stdout, r.stderr)

        def trial(name, reason, mutate=None, anchor=None, private=None, do_replay=False):
            repo = base / name
            mini_repo(repo)
            h = expected
            if mutate:
                h2 = mutate(repo)
                if isinstance(h2, str):
                    h = h2
            if anchor is not None:
                h = anchor
            r = run(repo, h, private, do_replay)
            assert r.returncode != 0 and r.stdout.strip() == 'REJECT: ' + reason, (name, r.stdout, r.stderr)
            results.append({'control': name, 'rejection': reason})

        rv = lambda repo: repo / REL
        ad = lambda repo: repo / 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r66'

        def reseal_author(repo):
            a = ad(repo)
            m = json.loads((a / 'MANIFEST.json').read_text())
            m['files'] = {k: sha((a / k).read_bytes()) for k in m['files']}
            (a / 'MANIFEST.json').write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')

        trial('wrong-anchor', 'REVIEW_MANIFEST_ANCHOR', anchor='0' * 64)
        trial('malformed-anchor', 'EXPECTED_ANCHOR', anchor='None')
        trial('edited-review', 'REVIEW_PAYLOAD_HASH',
              lambda repo: (rv(repo) / 'review.md').write_text('VERDICT: SUBSTANTIAL'))
        trial('edited-and-resealed-review', 'REVIEW_MANIFEST_ANCHOR',
              lambda repo: ((rv(repo) / 'review.md').write_text('VERDICT: SUBSTANTIAL'), seal(rv(repo)))[1] and None)
        trial('extra-review-file', 'REVIEW_FILE_MEMBERSHIP',
              lambda repo: (rv(repo) / 'forged-pass.txt').write_text('PASS'))
        trial('missing-review-file', 'REVIEW_FILE_MEMBERSHIP',
              lambda repo: (rv(repo) / 'review.md').unlink())
        trial('extra-review-directory', 'REVIEW_DIRECTORY_MEMBERSHIP',
              lambda repo: (rv(repo) / 'unexpected').mkdir())
        trial('review-symlink', 'REVIEW_SYMLINK',
              lambda repo: (rv(repo) / 'link').symlink_to(repo / 'sources/preprints-tree.json'))
        trial('author-candidate-changed', 'AUTHOR_CANDIDATE_ANCHOR',
              lambda repo: (ad(repo) / 'candidate.md').write_text('weakened candidate'))
        trial('author-scope-changed', 'AUTHOR_SCOPE_ANCHOR',
              lambda repo: (ad(repo) / 'original-scope.md').write_text('restricted series only'))
        trial('author-comparison-resealed', 'AUTHOR_MANIFEST_ANCHOR',
              lambda repo: ((ad(repo) / 'comparison.md').write_text('no antecedents'), reseal_author(repo)) and None)
        trial('author-extra-file', 'AUTHOR_MEMBERSHIP',
              lambda repo: (ad(repo) / 'independent-pass.md').write_text('PASS'))
        trial('author-file-edited', 'AUTHOR_PAYLOAD_HASH',
              lambda repo: (ad(repo) / 'reading-limits.md').write_text('read everything'))
        trial('tree-edited', 'TREE_ANCHOR',
              lambda repo: (repo / 'sources/preprints-tree.json').write_bytes(
                  (repo / 'sources/preprints-tree.json').read_bytes().replace(b'"truncated": false', b'"truncated": true', 1)
                  if b'"truncated": false' in (repo / 'sources/preprints-tree.json').read_bytes()
                  else (repo / 'sources/preprints-tree.json').read_bytes() + b' '))
        trial('source-copy-edited', 'SOURCE_GIT',
              lambda repo: (ad(repo) / 'private/build/sections/01-introduction.tex').write_text('r_n(G,H)=0'))
        trial('frozen-input-edited', 'INPUT_HASH',
              lambda repo: (repo / 'frontier/campaigns/2026-10-14/discovery-r66-parent/chain-obstruction.md').write_text('x'))
        if private_dir:
            def bad_private(repo):
                p = repo / 'private-copy'
                shutil.copytree(private_dir, p)
                f = next(x for x in sorted(p.iterdir()) if x.suffix == '.pdf')
                f.write_bytes(f.read_bytes() + b'\n')
            trial('private-body-edited', 'PRIVATE_HASH', bad_private,
                  private=base / 'private-body-edited' / 'private-copy')
        if replay:
            def forged_results(repo):
                d = json.loads((rv(repo) / 'diagnostic-results.json').read_text())
                d['C'][0]['ell'] = 5
                (rv(repo) / 'diagnostic-results.json').write_text(json.dumps(d, indent=1, sort_keys=True) + '\n')
                return seal(rv(repo))
            trial('self-consistent-forged-diagnostics', 'DIAGNOSTIC_REPLAY', forged_results, do_replay=True)
    return {'baseline': 'verified', 'reason_checked_controls': results, 'count': len(results),
            'limits': 'integrity controls on copies; not mathematics, not a contribution verdict'}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected', required=True)
    ap.add_argument('--private-dir', type=Path)
    ap.add_argument('--replay', action='store_true')
    a = ap.parse_args()
    print(json.dumps(main(a.expected, a.private_dir, a.replay), indent=2, sort_keys=True))
