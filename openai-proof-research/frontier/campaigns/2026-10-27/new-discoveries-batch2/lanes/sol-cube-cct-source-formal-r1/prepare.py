from pathlib import Path
import shutil,json
L=Path(__file__).resolve().parent
shutil.copyfile(L/'frozen/sol-median-temporal-source-formal-r1/pins.json',L/'pins.json')
s=(L/'frozen/sol-median-temporal-source-formal-r1/audit_verify.py').read_text()
s=s.replace("['FiniteCore','IntegerLeaf','Audit']","['Finite','Cube','Endpoint','Audit']")
s=s.replace("'source_endpoint_status':'NOT_PROVED','source_probability_defined':False", "'source_endpoint_status':'PROVED_N5','endpoint':'Cube.literal_question66_false'")
s=s.replace("'finite deterministic component and explicit integer leaves only; no 241-coefficient, stochastic, analytic or median-transfer PASS'", "'Unconditional n=5 literal Question6.6 negation for all real linear cube automorphisms; all-n extension not formalized; novelty HOLD'")
(L/'audit_verify.py').write_text(s)
(L/'run.sh').write_text('''#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for mod in Finite Cube Endpoint; do
 python lean_guard.py "$mod.log" -o "$mod.olean" "$mod.lean"
done
python lean_guard.py Audit.log Audit.lean
python "$guard" python audit_verify.py
''')
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text())
 print(name, 'keys:',list(d))
 for k in ['accepted','rejected','held']:
  for e in d.get(k,[]):
   print(k, e.get('number',e.get('title')),e.get('title'),e.get('status'))
