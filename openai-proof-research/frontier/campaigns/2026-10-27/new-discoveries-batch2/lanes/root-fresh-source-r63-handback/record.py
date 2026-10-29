import hashlib, itertools, json
from pathlib import Path
from datetime import datetime, timezone

here = Path(__file__).resolve().parent
batch = here.parent.parent
lane = batch / 'lanes/sol-fresh-source-discovery-r63'
prov = json.loads((lane / 'provenance.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = [{'path': k, 'expected': v, 'actual': sha(lane / k)} for k, v in prov['files'].items()]
mismatches = [r for r in rows if r['expected'] != r['actual']]
# Keep any post-finalization log mismatch explicit; never silently repair frozen evidence.
assert all(r['path'] in {'finalize.log', 'finalize-guard.json'} for r in mismatches), mismatches
assert (here / 'check-copy/checks.json').read_bytes() == (lane / 'checks.json').read_bytes()
supports = ((0,4,5), (0,3,5), (0,4,5), (0,1,5))
counts = {}
for d in (4,8):
    counts[d] = sum(sum(t)==d and all((t[i]-t[0]-i)%4 != 0 for i in range(1,4)) for t in itertools.product(*supports))
assert counts == {4:3, 8:5}
q = [0,0,0,0,1]
for n in range(5,23):
    q.append(sum(q[n-j] for j in supports[n%4] if j))
assert [q[n] for n in (22,18,14,10,6,2)] == [4,2,1,0,0,0]
collision = [(i-d)%4 for i,d in enumerate((0,3,0,1))]
assert collision == [0,2,2,2]
receipt = {
    'utc': datetime.now(timezone.utc).isoformat(),
    'decision': 'EXCLUDE discovery credit: printed coefficient-formulation correction',
    'credit': 0,
    'counts': {'additional':7, 'total':37},
    'ordinary_math': 'PASS for literal printed Conjecture 1; every signing fails by parity, including eventual reading via finite invertible phase-state orbit',
    'source_read': 'Cached published text Eq(1) p2 and Conjecture1 p16; PDF/Zenodo bytes recorded by worker. No fresh network or visual PDF check by root.',
    'root_validation': 'Own-copy complete worker checker PASS and byte-identical checks.json; separate tuple-count and integer-sequence assertions PASS',
    'reason': 'The printed exclusion checks only collisions with row zero, admitting (0,3,0,1) with column residues (0,2,2,2). Full pairwise column distinctness is the ordinary determinant permutation condition. This corrects the proposed coefficient formula and does not refute existence of the intended constant recurrence. No nonroutine residual result is nominated.',
    'strongest_countercase': 'An explicit conjecture in a published paper is literally false for every possible sign assignment; nevertheless the campaign expressly excludes coefficient/formulation repairs.',
    'limits': ['Closest 2014 theorem body unread; no claim that it already publishes this exact refutation.', 'Current registry freshness HOLD.', 'No full Lean, paper, independent final review, priority claim or acceptance.'],
    'input_hash_count': len(rows),
    'hash_mismatches': mismatches,
    'input_hashes': rows,
}
(here / 'ADOPTION.json').write_text(json.dumps(receipt, indent=2)+'\n')
nextp = batch / 'NEXT.md'
s = nextp.read_text()
s = s.replace('Three fresh Sol high/default research lanes r61 finite structures, r62 analysis,\nr63 arithmetic/algebra are active; no children.', 'r63 supplied a sound literal parity refutation of the printed Guday–Sahin\ncoefficient formula; root excludes it as a missing determinant-column restriction,\nwith source/prior-art holds preserved. See lanes/root-fresh-source-r63-handback/ADOPTION.json.\nThree fresh Sol high/default research lanes r61 finite structures, r62 analysis,\nr64 arithmetic/algebra are active; no children.')
nextp.write_text(s)
paths = [str(nextp.relative_to(Path.cwd()))]
paths += [str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name != 'pathspec.txt']
(here / 'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'checks':'PASS', 'hashes':len(rows), 'mismatches':mismatches, 'counts':[7,37]}))
