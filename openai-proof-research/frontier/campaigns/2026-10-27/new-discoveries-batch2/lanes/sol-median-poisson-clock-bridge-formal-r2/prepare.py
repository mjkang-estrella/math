from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
mods=['FiniteCore','IntegerLeaf','ClockMarginals','MarkedCounts']
s=(L/'frozen/Audit.lean').read_text().replace('import Lean','import ClockMarginals\nimport MarkedCounts\nimport Lean').replace('["FiniteCore", "IntegerLeaf"]','["FiniteCore", "IntegerLeaf", "ClockMarginals", "MarkedCounts"]')
(L/'failed-Audit-combined.lean.txt').write_text(s)
for tag, imports, audited in [('Finite',['FiniteCore','IntegerLeaf'],['FiniteCore','IntegerLeaf']),('Probability',['ClockMarginals','MarkedCounts'],['ClockMarginals','MarkedCounts'])]:
 a=s[s.index('set_option autoImplicit'):].replace('["FiniteCore", "IntegerLeaf", "ClockMarginals", "MarkedCounts"]',json.dumps(audited))
 (L/('Audit'+tag+'.lean')).write_text(''.join('import '+n+'\n' for n in imports)+a)
s=(L/'frozen/audit_verify.py').read_text().replace("['FiniteCore','IntegerLeaf','Audit']",repr(mods+['AuditFinite','AuditProbability'])).replace("(L/'Audit.log').read_text()","(L/'AuditFinite.log').read_text() + '\\n' + (L/'AuditProbability.log').read_text()").replace("if mod!='Audit':","if not mod.startswith('Audit'):").replace("'finite deterministic component and explicit integer leaves only; no 241-coefficient, stochastic, analytic or median-transfer PASS'","'finite core, integer leaves, actual initial product law, iid mark-prefix and independent count-prefix cylinder masses only; no Poisson clock realization or source PASS'")
(L/'audit_verify.py').write_text(s)
(L/'run.sh').write_text('''#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for mod in FiniteCore IntegerLeaf ClockMarginals MarkedCounts; do
  python lean_guard.py "$mod.log" -o "$mod.olean" "$mod.lean"
done
python lean_guard.py AuditFinite.log AuditFinite.lean
python lean_guard.py AuditProbability.log AuditProbability.lean
python "$guard" python audit_verify.py
''')
if (L/'Audit.lean').exists(): (L/'Audit.lean').rename(L/'failed-Audit.lean.txt')
names=[n+'.lean' for n in mods]+['AuditFinite.lean','AuditProbability.lean','audit_verify.py','run.sh','lean_guard.py','pins.json']
(L/'source-manifest.json').write_text(json.dumps({n:hashlib.sha256((L/n).read_bytes()).hexdigest() for n in names},indent=2)+'\n')
