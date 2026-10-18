#!/usr/bin/env python3
"""Reviewer-owned source-body comparison against the complete canonical preprint tree.

MIT. Read-only. Uses no author receipt file: every copied body under
private/preprints/ is hashed as a Git blob and compared to the tree entry
at the same pinned path, and every non-PDF blob of each touched manuscript
directory must be present. Identity only; says nothing about theorem truth.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet', required=True)
    ap.add_argument('--source-tree', required=True)
    ap.add_argument('--family', action='append', default=[])
    a = ap.parse_args()
    tree_path = Path(a.source_tree)
    if hashlib.sha256(tree_path.read_bytes()).hexdigest() != TREE_SHA256:
        raise ValueError('canonical tree hash mismatch')
    tree = json.loads(tree_path.read_text())
    if tree.get('truncated') is not False:
        raise ValueError('tree truncated')
    blobs = {e['path']: e for e in tree['tree'] if e['type'] == 'blob'}
    base = Path(a.packet) / 'private' / 'preprints'
    copied = {}
    for dirpath, dirnames, filenames in os.walk(base):
        for n in dirnames + filenames:
            st = os.lstat(os.path.join(dirpath, n))
            if stat.S_ISLNK(st.st_mode):
                raise ValueError('symlink in copied sources: ' + n)
        for n in filenames:
            p = Path(dirpath) / n
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise ValueError('nonregular or hardlinked source: ' + str(p))
            copied['preprints/' + p.relative_to(base).as_posix()] = git_blob(p.read_bytes())
    families = sorted({k.split('/')[1] for k in copied})
    for fam in a.family:
        if fam not in families:
            raise ValueError('required family absent: ' + fam)
    report = {}
    for fam in families:
        canon = {p: e['sha'] for p, e in blobs.items()
                 if p.split('/')[1] == fam and not p.endswith('.pdf')}
        have = {p: s for p, s in copied.items() if p.split('/')[1] == fam}
        missing = sorted(set(canon) - set(have))
        extra = sorted(set(have) - set(canon))
        wrong = sorted(p for p in set(have) & set(canon) if have[p] != canon[p])
        if missing or extra or wrong:
            raise ValueError(json.dumps({'family': fam, 'missing': missing, 'extra': extra, 'wrong': wrong}))
        pdfs = sorted(p for p in blobs if p.split('/')[1] == fam and p.endswith('.pdf'))
        report[fam] = {'non_pdf_blobs_matched': len(have), 'pdf_blobs_not_copied': len(pdfs)}
    print(json.dumps({'status': 'PASS', 'families': report,
                      'total_matched': sum(r['non_pdf_blobs_matched'] for r in report.values())},
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
