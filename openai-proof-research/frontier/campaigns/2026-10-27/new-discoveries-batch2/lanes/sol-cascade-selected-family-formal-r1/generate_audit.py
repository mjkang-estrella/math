from pathlib import Path
import re,json,resource,os
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
b=Path(__file__).resolve().parent
mods=['DepthDefs','SourceDefs','TreeConstruction','DepthArithmetic','DepthAnalysis','SelectedFamily','SelectedCounting']; names=[]
for m in mods:
 names += ['CascadeRate.'+n for n in re.findall(r'^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private)\s+)?(?:def|abbrev|theorem|structure)\s+(\w+)',(b/'formal'/f'{m}.lean').read_text(),re.M)]
names += ['CascadeRate.SourceContextTree.'+s for s in ['nodes','prefix_closed','root_internal','saturated','countable_branches']]
names += ['CascadeRate.ProbabilityAssignment.'+s for s in ['law','positive','normalized']]
assert len(names)==len(set(names))
(b/'declarations.json').write_text(json.dumps(names,indent=2)+'\n')
(b/'formal/Audit.lean').write_text('import SelectedCounting\nset_option autoImplicit false\nset_option warningAsError true\nset_option pp.universes true\n'+''.join(f'#check {n}\n#print axioms {n}\n' for n in names))
print('audit inventory',len(names))
