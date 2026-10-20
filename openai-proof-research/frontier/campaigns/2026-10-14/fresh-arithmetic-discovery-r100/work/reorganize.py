#!/usr/bin/env python3
"""One-shot packet reorganization for r100: contract layout + receipts. Author-side, run once."""
import hashlib, json, os, shutil, sys
from pathlib import Path

R = Path(__file__).resolve().parent.parent
REPO = R.parents[3]
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
RAW = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'
tree = {e['path']: e for e in json.loads((REPO / 'sources/preprints-tree.json').read_text())['tree']}
by_sha = {}
for p, e in tree.items():
    if e.get('type') == 'blob':
        by_sha.setdefault(e['sha'], []).append(p)

def blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

# (current local path, read_extent, retained?)
READS = {
 # totients 024 cluster
 'packet/private/source/totients024/statements.tex': ('full', True),
 'packet/private/source/totients024/companion.tex': ('full', True),
 'packet/private/source/intros/totients.tex': ('full', True),
 # prime-arguments paper
 'packet/private/source/primeargs/introduction.tex': ('full', True),
 'packet/private/source/primeargs/local.tex': ('full', True),
 'packet/private/source/primeargs/descent.tex': ('full', True),
 'packet/private/source/primeargs/tuples.tex': ('lines 1-64 and 495-511 (slot/cycle parameters, d=|V|, M_0 definition) plus targeted searches; not read line-complete', True),
 'packet/private/source/primeargs/kernel.tex': ('fetched; not read', False),
 'packet/private/source/primeargs/lifts.tex': ('fetched; not read', False),
 'packet/private/source/primeargs/primes.tex': ('fetched; not read', False),
 # integer intersective paper
 'packet/private/source/intersective/introduction.tex': ('full', True),
 'packet/private/source/intersective/tuples.tex': ('fetched; not read', False),
 'packet/private/source/intersective/kernel.tex': ('fetched; not read', False),
 'packet/private/source/intersective/lifts.tex': ('fetched; not read', False),
 'packet/private/source/intersective/transfer.tex': ('fetched; not read', False),
 'packet/private/source/intersective/induction.tex': ('fetched; not read', False),
 # 008 manuscript
 'packet/private/source/dd008/README.md': ('screening read', True),
 'packet/private/source/dd008/build/paper.tex': ('screening read', True),
 'packet/private/source/dd008/build/references.tex': ('skimmed for citations', True),
 'packet/private/source/dd008/build/sections/01-introduction.tex': ('full', True),
 'packet/private/source/dd008/build/sections/02-algebra.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/03-degeneration.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/04-deletion.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/05-image.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/06-category.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/07-holonomy.tex': ('screening read of statements and proofs', True),
 'packet/private/source/dd008/build/sections/08-induction.tex': ('screening read of statements and proofs', True),
 # intros
 'packet/private/source/intros/simprim.tex': ('screening read (introduction of the 029 companion paper)', True),
 'packet/private/source/intros/jacobsthal.tex': ('screening read (introduction, family 021)', True),
 'packet/private/source/intros/dickman.tex': ('screening read (introduction, family 012)', True),
 'packet/private/source/intros/duffin.tex': ('screening read (introduction, family 022)', True),
 'packet/private/source/intros/egyptian.tex': ('screening read (introduction, family 025)', True),
 'packet/private/source/intros/gauss-paper.tex': ('screening read (top-level paper file, family 023)', True),
 'packet/private/source/intros/modularity.tex': ('screening read (introduction, family 030)', True),
 'packet/private/source/intros/primegaps.tex': ('screening read (introduction, family 026)', True),
 'packet/private/source/intros/quartic.tex': ('screening read (introduction, family 020)', True),
 'packet/private/source/intros/bernoulli.tex': ('screening read (main file, family 153)', True),
 'packet/private/source/intros/vdw.tex': ('screening read (introduction, family 160)', True),
 # duplicate of intersective introduction: removed silently (same upstream path)
}

receipts = {}
src = R / 'packet/private/source'
out = R / 'packet/private/upstream'
for rel, (extent, keep) in sorted(READS.items()):
    p = R / rel
    b = p.read_bytes()
    gb = blob(b)
    ups = by_sha.get(gb)
    assert ups and len(ups) == 1, rel
    up = ups[0]
    e = tree[up]
    assert e['size'] == len(b), rel
    rec = {'upstream_path': up, 'git_blob': gb, 'tree_blob': e['sha'], 'size': len(b),
           'sha256': hashlib.sha256(b).hexdigest(), 'raw_url': RAW + up, 'read_extent': extent}
    receipts[rel] = (rec, keep)

# duplicate fetch: intros/intersective.tex has the same blob as intersective/introduction.tex
dup = src / 'intros/intersective.tex'
dup2 = src / 'intersective/introduction.tex'
assert dup.read_bytes() == dup2.read_bytes()

# Write retained to contract layout; delete removed.
for rel, (rec, keep) in receipts.items():
    p = R / rel
    if keep:
        dest = out / rec['upstream_path']
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(p), str(dest))
        os.chmod(dest, 0o644)
    else:
        rec['reason'] = 'fetched for the exponent-uniformity feasibility check; not read; local copy removed before sealing'
        p.unlink()

# delete the duplicate intros/intersective.tex
dup.unlink()

shutil.rmtree(src)
(R / 'packet/private/source').rmdir() if (R / 'packet/private/source').exists() else None
for d in ['primary', 'search']:
    dd = R / 'packet/private' / d
    if dd.exists() and not any(dd.iterdir()):
        dd.rmdir()

(R / 'work/source-receipts.json').write_text(json.dumps(
    {rel: {'rec': rec, 'retained': keep} for rel, (rec, keep) in receipts.items()}, indent=1))
print('retained', sum(1 for r in receipts.values() if r[1]), 'removed', sum(1 for r in receipts.values() if not r[1]))
