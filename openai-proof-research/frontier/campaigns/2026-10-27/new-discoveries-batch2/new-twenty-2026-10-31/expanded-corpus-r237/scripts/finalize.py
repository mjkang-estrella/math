from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];r=json.loads((L/'results.json').read_text())
for i in ['351235','351237','351238']:
 r[i]['additional_structured_attempt']={'output':'outputs/pn-structured-expanded.json','tested_pairs':210,'family':'theta graphs with three path lengths 2..8; n greater than every cycle and at most graph order','iteration_cap':10,'vertex_cap':32,'edge_cap':48,'outcome':'all reached size cap; no certified divergence or convergent hit'}
 r[i]['limitations'].append('This is finite orbit inspection, not an exhaustive search of all graphs or all minimal convergent subgraphs.')
for v in r.values():v['workflow_limitations']='Initial q-matroid diagnostics preceded completion of the correct Lean Pool projects manifest and all GitHub queries. No candidate was promoted; chronology is disclosed in SUMMARY.md.'
(L/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
manifest={}
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name!='manifest.json':manifest[str(p.relative_to(L))]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('finalized',len(r),'ID-keyed entries and',len(manifest),'files')
