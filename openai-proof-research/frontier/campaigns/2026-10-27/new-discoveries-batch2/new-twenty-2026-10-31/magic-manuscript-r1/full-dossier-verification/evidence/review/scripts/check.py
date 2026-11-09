from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[1];s=r.parent/'expanded-corpus-r75'
a=[3,2,4,5,8,6,1,7,9,10,11];es=[(i,(i+1)%7) for i in range(7)]+[(6,i) for i in range(7,11)]
def verify(a,c):return sorted(a)==list(range(1,12)) and sorted(c-a[u]-a[v] for u,v in es)==list(range(12,23))
assert verify(a,26);assert not verify(a,27);b=a.copy();b[0]=b[1];assert not verify(b,26)
assert (r/'extracted/Magic.lean').read_bytes()==(s/'formal/Magic.lean').read_bytes()
assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',(r/'extracted/Magic.lean').read_text())
log=(r/'logs/audit.log').read_text();assert log.count('DECL|')==37 and 'COUNT|37' in log and 'unsafe=true' not in log and 'partial=true' not in log and 'body=false' not in log
for n in ['build','audit','leanchecker']:assert json.loads((r/'receipts'/f'{n}.json').read_text())['exit']==0
out=dict(original_labeling=True,changed_constant_rejected=True,duplicate_vertex_label_rejected=True,source_zip_matches_formal=True,all_declarations=37,forbidden_token_scan='negative',exact_strength_ordinary=26,exact_strength_formalized=False)
(r/'logs/check.json').write_text(json.dumps(out,indent=2));print(out)
