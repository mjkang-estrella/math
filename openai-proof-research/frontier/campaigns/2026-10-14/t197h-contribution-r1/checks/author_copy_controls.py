#!/usr/bin/env python3
"""MIT. Controls on a DISPOSABLE copy of the frozen r49 packet; never touches the original.

Usage: author_copy_controls.py --original R49_DIR --work NEW_DIR_UNDER_/var/tmp --anchor HASH --tree PREPRINTS_TREE_JSON
"""
import argparse, hashlib, importlib.util, json, os, shutil, subprocess, sys
from pathlib import Path


def sha(b):
    return hashlib.sha256(b).hexdigest()


def gitblob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def main():
    p = argparse.ArgumentParser()
    for k in ('--original', '--work', '--anchor', '--tree'):
        p.add_argument(k, required=True)
    a = p.parse_args()
    orig = Path(a.original).resolve(); work = Path(a.work).absolute()
    assert str(work).startswith('/var/tmp/') and not work.exists(), 'work must be new and under /var/tmp'
    work.mkdir()
    canon = {e['path']: e['sha'] for e in json.load(open(a.tree))['tree'] if e['type'] == 'blob'}
    results = []

    def fresh(name):
        d = work / name
        shutil.copytree(orig, d, symlinks=True)
        return d

    def load(d):
        spec = importlib.util.spec_from_file_location('v_' + d.name.replace('-', '_'), d / 'verify.py')
        m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

    def attempt(name, d, anchor):
        try:
            load(d).check(d, anchor); return 'PASS'
        except Exception as e:
            return 'REJECT: ' + str(e)

    def record(name, expected, actual, note=''):
        ok = actual.startswith('PASS') == (expected == 'accept')
        results.append({'case': name, 'expected': expected, 'actual': actual, 'as_expected': ok, 'note': note})

    # Positive and wrong-anchor on a plain copy.
    d = fresh('positive'); record('positive_copy', 'accept', attempt('positive', d, a.anchor))
    record('wrong_anchor', 'reject', attempt('wrong', d, '0' * 64))

    # Author-supplied copied controls, run only inside a further disposable copy.
    d = fresh('author-controls')
    r = subprocess.run([sys.executable, '-B', str(d / 'checks' / 'integrity_controls.py'), '--root', str(d),
                        '--scratch', str(d / 'checks' / 'ctl-scratch')], capture_output=True, text=True)
    ctl = json.loads(r.stdout) if r.returncode == 0 else {'status': 'FAIL', 'stderr': r.stderr[-2000:]}
    record('author_integrity_controls_on_copy', 'accept', 'PASS' if ctl.get('status') == 'PASS' else 'REJECT: ' + str(ctl),
           note='%d author cases' % len(ctl.get('controls', [])))

    # Mutations of private source bodies and of the candidate.
    src = 'private/preprints/A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026/build/sections/planar.tex'
    d = fresh('changed-source'); f = d / src; f.write_bytes(f.read_bytes() + b'%x\n')
    record('changed_private_source_body', 'reject', attempt('cs', d, a.anchor))
    d = fresh('changed-candidate'); f = d / 'candidate.md'; f.write_bytes(f.read_bytes().replace(b'32/', b'33/', 1))
    record('changed_candidate_constant', 'reject', attempt('cc', d, a.anchor))

    # Copied-source trust: mutate a source body, rewrite receipts+selection+manifest consistently.
    d = fresh('reseal-source'); f = d / src; b = f.read_bytes() + b'%forged\n'; f.write_bytes(b)
    rec = json.loads((d / 'source197-receipts.json').read_text())
    for e in rec['files']:
        if e['local'] == src:
            e['git_blob_sha1'] = gitblob(b); e['sha256'] = sha(b); e['bytes'] = len(b); repo_path = e['path']
    (d / 'source197-receipts.json').write_text(json.dumps(rec, indent=2) + '\n')
    sel = json.loads((d / 'source-tree-selection.json').read_text())
    for e in sel['entries']:
        if e['path'] == repo_path:
            e['sha'] = gitblob(b)
    (d / 'source-tree-selection.json').write_text(json.dumps(sel, indent=2) + '\n')
    m = json.loads((d / 'MANIFEST.json').read_text())
    for e in m['files']:
        g = (d / e['path']).read_bytes(); e['bytes'] = len(g); e['sha256'] = sha(g)
    (d / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')
    self_anchor = sha((d / 'MANIFEST.json').read_bytes())
    record('forged_source_reseal_external_anchor', 'reject', attempt('fs', d, a.anchor))
    record('forged_source_reseal_self_anchor', 'accept', attempt('fs2', d, self_anchor),
           note='documents limit: author verifier trusts copied selection; only the external anchor protects')
    canon_ok = canon.get(repo_path) == gitblob(b)
    record('forged_source_vs_canonical_tree', 'reject', 'PASS' if canon_ok else 'REJECT: canonical blob mismatch',
           note='independent comparison against separately anchored preprints-tree.json')

    # Ancestor symlink: author verifier does not inspect ancestors.
    real = work / 'ancestor-real'; real.mkdir(); shutil.copytree(orig, real / 'pkt', symlinks=True)
    link = work / 'ancestor-link'; link.symlink_to(real, target_is_directory=True)
    record('ancestor_symlink_author_verifier', 'accept', attempt('al', link / 'pkt', a.anchor),
           note='documents limit: accepted through a symlinked ancestor')

    shutil.rmtree(work)
    allok = all(x['as_expected'] for x in results)
    print(json.dumps({'status': 'PASS' if allok else 'FAIL', 'cases': results,
                      'scope': 'Disposable /var/tmp copies only; identity/inventory behaviour, not mathematics.'}, indent=2))
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
