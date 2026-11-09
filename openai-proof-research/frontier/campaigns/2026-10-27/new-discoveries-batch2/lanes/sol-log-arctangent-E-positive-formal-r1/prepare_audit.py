import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for _threadvar in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
 os.environ[_threadvar]='1'
from pathlib import Path
import re,json
p=Path(__file__).resolve().parent
names=sorted(set(re.findall(r'DECL (\S+)',(p/'logs/Inventory.lean.log').read_text())))
(p/'declarations.json').write_text(json.dumps(names,indent=2)+'\n')
for i in range(0,len(names),50):
 # Identifiers with inaccessible Unicode or generated numeric name-components printed quoted
 text='import MeanEPositive\nimport FiniteAbel\nset_option autoImplicit false\nset_option warningAsError true\nset_option linter.auxLemma false\n'
 for n in names[i:i+50]:
  ident='.'.join('«'+s+'»' if s.isdigit() else s for s in n.split('.'))
  text+=f'#check {ident}\n#print axioms {ident}\n'
 (p/f'formal/Audit{i//50}.lean').write_text(text)
print(len(names))
