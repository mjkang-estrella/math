# Original independent audit helper, MIT; Myeongjin Kang, no affiliation.
from pathlib import Path
import re,json
p=Path(__file__).resolve().parent
s=(p/'work/CM275.lean').read_text()
names=re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\w+)',s,re.M)
assert names and len(names)==len(set(names))
(p/'work/TypeAudit.lean').write_text('import CM275\n'+''.join(f'#check CM275.{n}\n#print axioms CM275.{n}\n' for n in names))
(p/'working-declaration-list.json').write_text(json.dumps({'note':'Generated from current reviewer snapshot; final bytes must be revalidated.','declarations':names},indent=2)+'\n')
print(len(names),'declarations')
