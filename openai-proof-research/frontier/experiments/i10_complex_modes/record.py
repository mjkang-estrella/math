"""Byte provenance only; no mathematical truth check and no shared writes."""
import datetime
import hashlib
import json
from pathlib import Path
import urllib.request

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i10_complex_modes'
OUT.mkdir(parents=True, exist_ok=True)
pin = json.loads((ROOT / 'sources/upstream.json').read_text())['commit']
tree = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
assert tree['truncated'] is False
entries = {r['path']: r for r in tree['tree']}
sha = lambda b: hashlib.sha256(b).hexdigest()

inputs = ['AGENTS.md', 'sources/upstream.json', 'sources/preprints-tree.json',
          'sources/CONTENTS.md', 'frontier/iterations/i07-arithmetic.md',
          'frontier/iterations/i05-parity-pd.md', 'frontier/reviews/i05-parity-pd-r2.md',
          'frontier/sources/i07_arithmetic/source-locators.json',
          'frontier/sources/i07_arithmetic/retrieval-manifest.json']
snapshot = [{'path': p, 'sha256': sha((ROOT / p).read_bytes())} for p in inputs]
snapfile = OUT / 'input-snapshot.json'
if not snapfile.exists():
    snapfile.write_text(json.dumps(snapshot, indent=2) + '\n')
changed = [p['path'] for p in json.loads(snapfile.read_text())
           if sha((ROOT / p['path']).read_bytes()) != p['sha256']]

old = json.loads((ROOT / inputs[-1]).read_text())
verified = []
for r in old['files']:
    b = (ROOT / r['local']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
    assert sha(b) == r['sha256'] and blob == r['git_blob'] == entries[r['path']]['sha']
    assert r['url'] == f'https://raw.githubusercontent.com/openai/math/{pin}/{r["path"]}'
    verified.append(r)

selection = {
    'The-Poisson-Dirichlet-Law': ['02-preliminaries.tex', '03-determinant.tex',
                                '06-correlations.tex', '07-extraction.tex',
                                '09-long-prime-appendix.tex'],
    'Weighted-Dilation-Graphs': ['02-transference.tex', '03-ideal-kernels.tex'],
    'Primitive-roots-for-every': ['08-type-ii.tex'],
    'The-Quasi-Riemann-Hypothesis-September': ['paper.tex'],
    'Ordinary-two-point': ['introduction.tex'],
    'Prime-Predecessors-with-an-Even': ['03-shifted.tex'],
}
retained = []
for r in verified:
    if not any(k in r['path'] and Path(r['path']).name in names for k, names in selection.items()):
        continue
    dest = OUT / 'pinned' / r['path']
    dest.parent.mkdir(parents=True, exist_ok=True)
    if not dest.exists():
        b = urllib.request.urlopen(r['url'], timeout=45).read()
        assert sha(b) == r['sha256']
        dest.write_bytes(b)
    assert sha(dest.read_bytes()) == r['sha256']
    retained.append({**r, 'local': str(dest.relative_to(ROOT)), 'fresh_raw_retrieval': True})

lit = []
for name, url in [
    ('selberg-delange-v8', 'https://arxiv.org/pdf/2010.12929v8'),
    ('granville-shao-v1', 'https://arxiv.org/pdf/1706.05710v1')]:
    for ext in ['pdf', 'txt']:
        src = ROOT / f'frontier/sources/i07_arithmetic/literature/{name}.{ext}'
        dest = OUT / 'literature' / src.name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(src.read_bytes())
        lit.append({'local': str(dest.relative_to(ROOT)), 'sha256': sha(dest.read_bytes()),
                    'primary_url': url, 'origin': str(src.relative_to(ROOT)),
                    'web_statement_reopened': True})

locators = []
labels = {'thm:type-II', 'det:cauchy-square', 'prop:graph-transfer', 'prop:ideal-family',
          'cor:list-norm', 'cor:stripped', 'cor:shared-collision', 'lem:divisor-model',
          'cor:SM', 'cor:sparse-bound', 'cor:constant-high', 'lem:block-sieve',
          'lem:progressions', 'ext:active-term', 'ext:allocation-core',
          'ext:allocation-identity', 'ext:prime-deweight-square',
          'lp:log-phase', 'lp:prime-polynomial', 'thm:main',
          'cor:transference-pairing', 'lem:marked-coefficient-transfer'}
import re
for r in retained:
    lines = (ROOT / r['local']).read_bytes().splitlines(keepends=True)
    for i, line in enumerate(lines):
        for label in re.findall(rb'\\label\{([^}]+)\}', line):
            if label.decode() in labels:
                lo, hi = max(0, i - 3), min(len(lines), i + 80)
                locators.append({'source': r['local'], 'label': label.decode(),
                                 'label_line': i + 1, 'start_line': lo + 1,
                                 'end_line': hi, 'sha256': sha(b''.join(lines[lo:hi]))})

for filename, obj in [('retrieval-manifest.json', {'pin': pin, 'files': retained}),
                      ('literature-manifest.json', lit), ('source-locators.json', locators),
                      ('verification.json', {'tree_entries': len(entries), 'tree_truncated': False,
                       'i07_retained_blobs_checked': len(verified), 'fresh_pinned_files': len(retained),
                       'input_changes': changed, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()})]:
    (OUT / filename).write_text(json.dumps(obj, indent=2) + '\n')
artifacts = [ROOT / 'frontier/iterations/i10-complex-prime-modes.md']
artifacts += list(OUT.rglob('*')) + list((ROOT / 'frontier/experiments/i10_complex_modes').rglob('*'))
rows = [{'path': str(p.relative_to(ROOT)), 'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
        for p in sorted(set(artifacts)) if p.is_file() and p.name != 'artifact-hashes.json']
(OUT / 'artifact-hashes.json').write_text(json.dumps(rows, indent=2) + '\n')
print(json.dumps({'checked_i07': len(verified), 'retained': len(retained),
                  'artifacts': len(rows), 'input_changes': changed}))
