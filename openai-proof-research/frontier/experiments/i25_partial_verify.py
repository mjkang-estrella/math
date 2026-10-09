"""Read-only partial I25 audit; finite diagnostics, never a proof certificate."""
from pathlib import Path
from decimal import Decimal, localcontext
import hashlib
import json

BASE = Path(__file__).resolve().parents[2]
PARTIAL = BASE / 'frontier/experiments/i25_matching_entropy_improvement'

def inventory():
    rows = []
    for kind in ('sources', 'experiments'):
        root = BASE / f'frontier/{kind}/i25_matching_entropy_improvement'
        for p in sorted(root.rglob('*')):
            if p.is_file():
                b = p.read_bytes()
                rows.append(dict(path=str(p.relative_to(BASE)), bytes=len(b), sha256=hashlib.sha256(b).hexdigest()))
    return rows

def evaluate(row):
    edges = row['edges']
    def enumerate_matchings(vertices):
        if not vertices:
            yield ()
            return
        u = min(vertices)
        for i, (a, b) in enumerate(edges):
            v = b if a == u else a if b == u else None
            if v is not None and v != u and v in vertices:
                for tail in enumerate_matchings(vertices - {u, v}):
                    yield (i,) + tail
    matches = list(enumerate_matchings(set(range(row['n']))))
    assert len(matches) == row['N']
    with localcontext() as ctx:
        ctx.prec = 70
        theta = [Decimal(str(x)) for x in row['theta']]
        weights = [sum((theta[i] for i in m), Decimal(0)).exp() for m in matches]
        z = sum(weights)
        probs = [w/z for w in weights]
        means = [sum((p for p, m in zip(probs, matches) if i in m), Decimal(0)) for i in range(len(edges))]
        def ent(values):
            return -sum((x*x.ln() for x in values if x), Decimal(0))
        h, f = ent(probs), ent(means)
        b = ent([1-x for x in means])
        w = ent([1-x for x, e in zip(means, edges) if row.get('v') not in e]) if 'v' in row else b
        ratio = (f-h)/w if w else Decimal(0)
        return dict(matchings=len(matches), H=str(h), F=str(f), denominator=str(w), ratio=str(ratio), stored_ratio=row.get('rooted_ratio', row.get('ratio')), tiny_denominator=w < Decimal('1e-9'))

def main():
    before = inventory()
    results = {}
    for name in ('search-results.json', 'structured-results.json', 'rooted-results.json'):
        data = json.loads((PARTIAL/name).read_text())
        rows = data.get('records', data.get('rows', []))
        results[name] = dict(saved_rows=len(rows), saved_top=len(data['top']), recomputed=[evaluate(r) for r in data['top']])
        if name == 'search-results.json':
            assert len(rows) == data['graphs'] == 311
            assert sum(7 if r['optimized'] else 5 for r in rows) == data['gibbs_laws'] == 1847
        if name == 'structured-results.json':
            assert len(rows) == data['perturbation_laws'] == 140
            results[name]['saved_blocks'] = len(data['blocks'])
    assert before == inventory(), 'Partial evidence changed during read-only audit'
    out = BASE / 'frontier/experiments'
    (out/'i25-interrupted-checkpoint.json').write_text(json.dumps(dict(status='cancelled-before-report', artifacts=before), indent=2)+'\n')
    (out/'i25-partial-parent-verification.json').write_text(json.dumps(dict(status='partial-only', precision=70, limitations='Independent enumeration of 33 saved top Gibbs laws at decimal-rounded saved parameters; decimal arithmetic is not directed interval certification. Full searches and source provenance not yet verified. No mathematical acceptance.', original_files_unchanged=True, results=results), indent=2)+'\n')
    print(json.dumps(dict(files_preserved=len(before), saved_top_laws=sum(r['saved_top'] for r in results.values()), rooted_top=results['rooted-results.json']['recomputed'][0]), indent=2))

if __name__ == '__main__':
    main()
