"""Prepare bindings; never runs diagnostics or creates a seal."""
import json,hashlib
from pathlib import Path
BASE=Path(__file__).resolve().parent;ROOT=BASE.parents[2];S=ROOT/'frontier/sources/i170_quadrilateral_coefficient'
assert not (BASE/'seal.json').exists(),'a sealed iteration must never be prepared again'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_text(json.dumps(d,sort_keys=True,indent=2)+'\n')
contexts=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
previous=ROOT/'frontier/experiments/i169_bridge_independence'
external={z['path'] for z in json.loads((previous/'inventory.json').read_text())['files']}
external.update(z['path'] for z in json.loads((ROOT/'frontier/sources/i169_bridge_independence/external-bindings.json').read_text())['files'])
external.update(str(p.relative_to(ROOT)) for p in [previous/'inventory.json',previous/'prevalidation.json',previous/'seal.json'])
external.update(contexts);external.add('sources/preprints-tree.json')
save(S/'external-bindings.json',{'files':[{'path':s,'sha256':sha(ROOT/s),'size':(ROOT/s).stat().st_size,'role':'context-only' if s in contexts else 'bound input'} for s in sorted(external)]})
save(S/'replay-policy.json',{'context_only_exclusions':contexts,'scope':'Only shared ledgers are context; all graph, theorem, ancestor, owned and report bytes are binding.','control_chain':'inventory excludes itself, prevalidation and seal; seal binds inventory and successful prevalidation; external supplied seal SHA authenticates the chain.','runtime':'Trusted Python standard library; diagnostics: python3 -I -B; no third-party packages and no diagnostic network.'})
old=json.loads((ROOT/'frontier/sources/i169_bridge_independence/external-bindings.json').read_text())['files']
save(S/'context-drift-preparation.json',[{'path':z['path'],'inherited':z['sha256'],'current':sha(ROOT/z['path']),'status':'drift' if sha(ROOT/z['path'])!=z['sha256'] else 'unchanged'} for z in old if z['path'] in contexts])
controls={BASE/'inventory.json',BASE/'prevalidation.json',BASE/'seal.json'}
report=ROOT/'frontier/iterations/i170-quadrilateral-coefficient.md'
files=sorted([report]+[p for d in (BASE,S) for p in d.rglob('*') if p.is_file() and p not in controls])
save(BASE/'inventory.json',{'iteration':170,'report':str(report.relative_to(ROOT)),'files':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p),'size':p.stat().st_size} for p in files]})
print('Prepared',len(files),'owned files and',len(external),'external bindings; no diagnostics executed.')
