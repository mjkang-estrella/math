#!/usr/bin/env python3
"""Reviewer-written identity check for the T205M manuscript packet.

Read-only. Independent of the packet's verify.py: own directory walk, own
Git blob computation against the canonical complete preprint tree, and
byte comparison of every provenance copy against its repository original.
Identity only; no mathematical verdict.  SPDX-License-Identifier: MIT
"""
import hashlib, json, os, stat, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]          # openai-proof-research
CAMP = ROOT / 'frontier/campaigns/2026-10-14'
PKT = CAMP / 't205m-manuscript-v1'
ANCHORS = {
    'manuscript_manifest': ('t205m-manuscript-v1/manifest.json',
                            '88bf34ebfd3a0dd4d98a2c3bb1da76820bd30b5b17e2fecb8d5f5248bd782f26'),
    'article_tex': ('t205m-manuscript-v1/public/article.tex',
                    '035d5cc246ba742555d1d2ccb2b3bec343821b77366bf75078000bbd518cfbe1'),
    'article_pdf': ('t205m-manuscript-v1/output/pdf/article.pdf',
                    '4144bf0f3f06b5a7e8a13e2937f03f9bc405101cf40a219e3a097fcc3a234765'),
    'public_inventory': ('t205m-manuscript-v1/public-source-inventory.json',
                         'd0bc6f05f0a7ebdb9a59c761ecb47571a30a202ad75e89ad976c0ebe0fae56c5'),
    'author_manifest': ('fresh-arithmetic-discovery-r38/manifest.json',
                        '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9'),
    'author_candidate': ('fresh-arithmetic-discovery-r38/candidate205m.md',
                         '17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5'),
    'author_scope': ('fresh-arithmetic-discovery-r38/scope205m.md',
                     '3eb9d790999b419a4083ead2a3ed0979217a36a12bdd78ceabe7fa6d3afb64f6'),
    'proof_review_manifest': ('t205m-proof-r1/manifest.json',
                              '4b41e5dd7cd63401630fade2451fae8a341b0f21f62e5b92a96561aa89674343'),
    'contribution_review_manifest': ('t205m-contribution-r1/manifest.json',
                                     'e70b5707f7787dbeaa155f4540d51358d5db8fcb4f4850c15c9328735baa526a'),
    'formal_manifest': ('t205m-formal-v1/manifest.json',
                        '3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2'),
    'formal_review_manifest': ('t205m-formal-review-r1/review-manifest.json',
                               '5824a6bd5b1fa6c87774b7d0e496f0cda8fe80005c00a98a51987c701cea4ea7'),
    'finite_certificate': ('t205m-manuscript-v1/public/code/finite-proof-certificate.json',
                           '5ffb18808a16add627497b29c82ee389187ad8f4d6df0f6fa52cc6ab49d99263'),
}
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
KSS_FRESH = Path('/var/tmp/t205m-msr1-work/primary/kss-9901037v1.pdf')


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def walk(root):
    files, dirs, bad = {}, [], []
    for dp, dn, fn in os.walk(root, followlinks=False):
        for d in dn:
            p = Path(dp, d)
            if p.is_symlink():
                bad.append('symlink dir ' + str(p))
            dirs.append(p.relative_to(root).as_posix())
        for f in fn:
            p = Path(dp, f)
            st = os.lstat(p)
            if not stat.S_ISREG(st.st_mode):
                bad.append('nonregular ' + str(p))
                continue
            if st.st_nlink != 1:
                bad.append('hardlink ' + str(p))
            files[p.relative_to(root).as_posix()] = {'bytes': st.st_size, 'sha256': sha(p)}
    return files, sorted(dirs), bad


def main():
    out = {'checks': {}, 'failures': []}
    def check(name, ok, detail=None):
        out['checks'][name] = {'pass': bool(ok), 'detail': detail}
        if not ok:
            out['failures'].append(name)

    for k, (rel, h) in ANCHORS.items():
        got = sha(CAMP / rel)
        check('anchor:' + k, got == h, got)

    man = json.loads((PKT / 'manifest.json').read_text())
    files, dirs, bad = walk(PKT)
    files.pop('manifest.json')
    check('inventory:no_links_or_nonregular', not bad, bad)
    check('inventory:files_equal_manifest', files == man['files'],
          {'actual': len(files), 'manifest': len(man['files'])})
    check('inventory:dirs_equal_manifest', dirs == man['directories'],
          {'actual': len(dirs), 'manifest': len(man['directories'])})
    check('inventory:counts_183_payload_36_dirs', len(files) == 183 and len(dirs) == 36,
          [len(files), len(dirs)])

    pub = json.loads((PKT / 'public-source-inventory.json').read_text())['files']
    pub_actual = {r[len('public/'):]: v for r, v in files.items() if r.startswith('public/')}
    check('public:inventory_equal', pub == pub_actual, sorted(pub_actual))

    tree = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
    check('tree:anchor', sha(ROOT / 'sources/preprints-tree.json') == TREE_SHA256)
    check('tree:complete', tree['truncated'] is False and len(tree['tree']) == 13223,
          [tree['truncated'], len(tree['tree'])])
    idx = {e['path']: e for e in tree['tree']}
    srcs = sorted(r for r in files if r.startswith('private/preprints/'))
    mism = []
    for r in srcs:
        b = (PKT / r).read_bytes()
        e = idx.get(r[len('private/'):])
        if not e or e['sha'] != blob(b) or e['size'] != len(b):
            mism.append(r)
    check('sources:21_blobs_match_canonical_tree', len(srcs) == 21 and not mism,
          {'count': len(srcs), 'mismatch': mism})

    rec = json.loads((PKT / 'provenance/copy-receipts.json').read_text())
    bad_copies = []
    for e in rec:
        c, o = PKT / e['copy'], ROOT / e['original']
        if not c.exists() or not o.exists() or c.read_bytes() != o.read_bytes() or sha(c) != e['sha256']:
            bad_copies.append(e['copy'])
    check('provenance:all_copies_byte_equal_repository_originals', not bad_copies,
          {'receipts': len(rec), 'bad': bad_copies})

    for e in json.loads((PKT / 'input-anchors.json').read_text()):
        same = (PKT / e['copy']).read_bytes() == (ROOT / e['original']).read_bytes()
        check('input_anchor:' + e['name'], same and sha(PKT / e['copy']) == e['sha256'], e['sha256'])

    prim = {e['path']: e for e in json.loads((PKT / 'primary-receipts.json').read_text())}
    kss = prim['private/primary/kss-9901037v1.pdf']
    if KSS_FRESH.exists():
        check('primary:kss_fresh_arxiv_download_equals_private_copy',
              sha(KSS_FRESH) == kss['sha256'] == sha(PKT / kss['path']), sha(KSS_FRESH))
    else:
        check('primary:kss_fresh_arxiv_download_equals_private_copy', False, 'fresh download absent')

    for name, cp in (('i19', 'provenance/i19-fresh-structural-discovery.md'),
                     ('i21', 'provenance/i21-signed-saxl-dominance.md')):
        orig = ROOT / 'frontier/iterations' / Path(cp).name
        check('credit_copy:' + name, (PKT / cp).read_bytes() == orig.read_bytes(), sha(orig))

    out['result'] = 'PASS_REVIEWER_IDENTITY' if not out['failures'] else 'FAIL_REVIEWER_IDENTITY'
    print(json.dumps(out, indent=1, sort_keys=True))
    sys.exit(0 if not out['failures'] else 1)


if __name__ == '__main__':
    main()
