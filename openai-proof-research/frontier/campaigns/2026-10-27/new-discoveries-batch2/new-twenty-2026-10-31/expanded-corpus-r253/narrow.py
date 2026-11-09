from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
j=json.loads((L/'deep-plan.json').read_text());j=[x for x in j if 'preprints-full' in x[0] or 'specific' in x[0] or re.search(r'FazekasAbelianSquare|NarayanaStrip/CiglerCycleWalk\.md|NarayanaStrip/CiglerStripExpansion\.md|FiniteGraphEntropy\.md',x[1])]
(L/'narrow-plan.json').write_text(json.dumps(j));print(len(j))
