exec((__import__('pathlib').Path(__file__).parent/'bootstrap.py').read_text().split('for n in')[0])
M=B.parent.parent/'2026-10-14/formal/.lake/packages/mathlib'
# Freeze probability/PMF interfaces before scientific inspection; no historical evidence trees.
for root in [M/'Mathlib/Probability',M/'Mathlib/MeasureTheory/Measure/ProbabilityMeasure',M/'Mathlib/MeasureTheory/Constructions/Pi.lean']:
 for p in ([root] if root.is_file() else sorted(root.rglob('*.lean'))):
  freeze(p,L/'library'/p.relative_to(M))
for p in (M/'Mathlib').rglob('*PMF*'):
 if p.is_dir():
  for q in sorted(p.rglob('*.lean')): freeze(q,L/'library'/q.relative_to(M))
freeze(B.parent.parent/'2026-10-14/formal/lake-manifest.json',L/'library/lake-manifest.json')
freeze(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'),L/'toolchain/lean')
(L/'library-freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'library bindings')
