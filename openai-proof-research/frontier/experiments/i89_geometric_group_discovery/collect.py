#!/usr/bin/env python3
"""Research capture only; never invoked by the read-only verifier."""
from pathlib import Path
import json,hashlib,re,subprocess,urllib.request,datetime
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i89_geometric_group_discovery'
def dump(n,v): (S/n).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
D=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
patterns={
 'ggt':r'Baumslag|one.relato|Boone.Higman|hyperbolic group|CAT\(?\s*0|CAT\\?\(0|CATzero|\\CAT',
 'effective_relative':r'(effective|computable|algorithm|recursive|quantitative|prescribed|relative).{0,100}(hyperbol|relator|special|subgroup|CAT|envelope|filling)|(hyperbol|relator|special|subgroup|CAT|envelope|filling).{0,100}(effective|computable|algorithm|recursive|quantitative|prescribed|relative)',
 'fixed_energy':r'energy.minimi|fixed.point.{0,65}(CAT|ultralimit|random group)|geometric.action|finite.residual|common.multiple|least.common.multiple',
}
hits={k:[] for k in patterns};rx={k:re.compile(v,re.I) for k,v in patterns.items()}
for d in D:
 for n,line in enumerate((R/d['local']).read_text(errors='replace').splitlines(),1):
  for k,p in rx.items():
   if p.search(line):hits[k].append({'path':d['path'],'local':d['local'],'line':n,'text':line})
rec=[]
for k,v in hits.items():
 dump('search-'+k+'.json',v);p='frontier/sources/i89_geometric_group_discovery/search-'+k+'.json'
 rec.append({'name':k,'pattern':patterns[k],'flags':'IGNORECASE','output':p,'count':len(v),'sha256':sha((R/p).read_bytes())})
dump('searches.json',rec)
families=['Baumslag-Solitar-free','Virtual-compact-specialness','A-hyperbolic-group-with-no','a-torsion-free-hyperbolic','Finite-algebraic-envelopes','Simple-F-infinity','An-Artin-group-with-no']
dump('selected-domain.json',[d for d in D if any(d['path'].split('/')[1].startswith(f) for f in families)])
inv=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R)
(S/'corpus-rg-files.txt').write_bytes(inv)
inputs=[]
for p in ['AGENTS.md','README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:
 q='frontier/sources/i89_geometric_group_discovery/snapshots/'+p
 inputs.append({'path':p,'snapshot':q,'mutable':p!='AGENTS.md','sha256':sha((R/q).read_bytes())})
dump('inputs.json',inputs)
refs=['sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json']
refs+=['frontier/iterations/'+p for p in ['i07-structures.md','i13-fresh-discovery.md','i15-odd-order-topology-resumed.md','i19-fresh-structural-discovery.md','i21-signed-saxl-dominance.md','i82-measured-group-operator-discovery.md','i84-abstract-close-algebras.md']]
refs+=['frontier/reviews/'+p for p in ['i07-structures-novelty-r3.md','i15-odd-order-topology-novelty-r3.md']]
dump('immutable-references.json',[{'path':p,'sha256':sha((R/p).read_bytes())} for p in refs])
print(json.dumps({'search_counts':{k:len(v) for k,v in hits.items()},'selected':len(json.loads((S/'selected-domain.json').read_text()))}))
