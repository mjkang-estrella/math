from pathlib import Path
import json,hashlib
L=Path.cwd(); base=L.parent.parent; repo=base.parents[3]
more=[base/'ledger.json',base/'prior-campaign-context.json',repo/'sources/upstream.json',repo/'sources/CONTENTS.md',repo/'sources/preprints-tree.json']
a=[]
for p in more:
 b=p.read_bytes();a.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(L/'administrative-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
p=L/'Witness.lean';s=p.read_text().replace('theorem avoid_p', '''theorem total_five_card : (wordUniverse 5).card = 541 := by
  rw [wordUniverse, List.toFinset_card_of_nodup ((nodup_allWords 5 5).filter packedB)]
  exact total_five
theorem avoid_p''');s=s.replace('theorem literal_source_claim_false', '''theorem contain_p : ((wordUniverse 5) \\ avoiders 5 [1,1,2,2]).card = 21 := by
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), total_five_card, avoid_p]
theorem contain_q : ((wordUniverse 5) \\ avoiders 5 [1,1,1,2]).card = 19 := by
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), total_five_card, avoid_q]
theorem literal_source_claim_false''');p.write_text(s)
# Convert set difference ASCII slash into Lean unicode.
p.write_text(p.read_text().replace(') \\ avoiders', ') ∖ avoiders'))
(L/'Audit.lean').write_text((L/'Audit.lean').read_text())
orig=L.parent/'sol-das-ap-irreducible-source-formal-r1/audit_verify.py'
# Bound before reading the newly needed utility.
b=orig.read_bytes();(L/'audit-tool-binding.json').write_text(json.dumps({'path':str(orig),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)},indent=2)+'\n')
s=b.decode().replace('Das.literal_universal_bound_false','Cayley.literal_source_claim_false').replace('PROVED_LITERAL_N5_REFUTATION','PROVED_LITERAL_CONJECTURE_8_8_REFUTATION').replace('Unconditional literal universal Conjecture5.1 negation via n5','Unconditional published strict-index Conjecture 8.8 negation via p1122 q1112 n5')
(L/'audit_verify.py').write_text(s)
(L/'run.sh').write_text('''#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python3 -B "$guard" python3 -B verify_pins.py > pins-before.json
for mod in Definitions Witness; do
  python3 -B lean_guard.py "$mod.log" -o "$mod.olean" "$mod.lean"
done
python3 -B lean_guard.py Audit.log Audit.lean
python3 -B "$guard" python3 -B audit_verify.py
python3 -B "$guard" python3 -B verify_pins.py > pins-after.json
''')
