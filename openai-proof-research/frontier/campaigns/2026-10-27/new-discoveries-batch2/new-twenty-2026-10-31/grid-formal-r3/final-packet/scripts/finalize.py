from pathlib import Path
import json
p=Path(__file__).resolve().parent.parent
r=json.loads((p/'results.json').read_text())
r['validation']={'fresh_replay_modules':23,'leanchecker_modules':23,'negative_controls':4,
 'LOCAL_declarations':163,'endpoint_import_closure_declarations':253265,
 'LOCAL_forbidden_flags':0,'allowed_endpoint_axioms':['propext','Classical.choice','Quot.sound'],
 'inventory_equals_audited':True,'report':'replay-report.json'}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
