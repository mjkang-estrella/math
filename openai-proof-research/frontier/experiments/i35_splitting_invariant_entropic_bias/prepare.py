"""Record only I35-owned metadata. Corpus and previous rounds are read-only."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i35_splitting_invariant_entropic_bias';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def read(p):return json.loads((R/p).read_text())
def write(name,v):(S/name).write_text(json.dumps(v,indent=2)+'\n')
def ident(p):
 b=(R/p).read_bytes();return dict(path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
# Earlier passages that were printed before the logging reader was installed.
manual=[('AGENTS.md',1,None),('frontier/TEN-FINDINGS.md',1,75),('frontier/iterations/iteration32-geometric-relativity-discovery-task.json',1,None),('frontier/iterations/iteration33-density-robust-brenier-task.json',1,None),('frontier/iterations/iteration35-splitting-invariant-entropic-bias-task.json',1,None),('frontier/iterations/i32-geometric-relativity-discovery.md',1,142),('frontier/iterations/i33-density-robust-brenier.md',1,None),('frontier/iterations/i34-target-uniform-brenier.md',1,None),('frontier/sources/i33_density_robust_brenier/literature/dnwp-v1.txt',250,490),('frontier/sources/i33_density_robust_brenier/literature/dnwp-v1.txt',885,1010)]
log=read(str((S/'read-passages.json').relative_to(R)))
for p,a,b in manual:
 lines=(R/p).read_text().splitlines(keepends=True);b=b or len(lines);row=dict(path=p,start_line=a,end_line=b,sha256=hashlib.sha256(''.join(lines[a-1:b]).encode()).hexdigest(),note='Printed in initial reads; full reports read in successive overlapping chunks. Hashing is not semantic reading.')
 if not any((x['path'],x['start_line'],x['end_line'])==(p,a,b) for x in log):log.append(row)
write('read-passages.json',log)
selected=read('frontier/sources/i34_target_uniform_brenier/source-manifest.json');write('source-manifest.json',selected)
# Reuse only the required primary PDF/text pairs and preserved historical failures.
texts={x['path'] for x in log if '/literature/' in x['path']}
manifest_paths=list((R/'frontier/sources/i33_density_robust_brenier/literature').glob('manifest*.json'))+[R/'frontier/sources/i34_target_uniform_brenier/fresh-retrievals.json',R/'frontier/sources/i34_target_uniform_brenier/fresh-extra.json']
primary=[];seen=set();used_manifests=set()
for mp in manifest_paths:
 for row in json.loads(mp.read_text()):
  if row.get('extraction',{}).get('path') in texts or row.get('path','').endswith(('dnwp-published.pdf','bk-published.pdf')):
   if row['path'] not in seen:primary.append(row);seen.add(row['path']);used_manifests.add(str(mp.relative_to(R)))
write('reused-primary.json',primary)
deps={'sources/preprints-tree.json','sources/CONTENTS.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json','frontier/sources/i34_target_uniform_brenier/source-manifest.json','frontier/sources/i34_target_uniform_brenier/artifact-seal.json','frontier/sources/i34_target_uniform_brenier/audit-verdicts.json','frontier/sources/i34_target_uniform_brenier/provenance-notes.json','frontier/sources/i33_density_robust_brenier/provenance-notes.json'}|texts|used_manifests
for p in primary:
 deps.add(p['path'])
 if 'extraction' in p:deps.add(p['extraction']['path'])
write('dependency-manifest.json',[ident(p) for p in sorted(deps)])
# Source contracts name the actual operation; no entire proof is certified by a hash.
contracts=[]
for row in read('frontier/sources/i34_target_uniform_brenier/contracts.json'):
 p=row['path']
 if p in texts or 'Sharp-One-Third-Stability' in p:
  contracts.append(row)
write('contracts.json',contracts)
tree=read('sources/preprints-tree.json');manuscripts=[x['path'] for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1];cat=(R/'sources/CONTENTS.md').read_text();links=re.findall(r'\]\((preprints/[^)]+)\)',cat)
transport=[p for p in manuscripts if any(w in p.lower() for w in ['brenier','entropic','transport'])]
write('inventory-screen.json',dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',complete_tree_truncated=tree['truncated'],manuscripts=len(manuscripts),catalogue_entries=len(links),transport_title_screen=transport,scope='Complete inventory parsed; title screening is not proof reading. BT source interfaces are separately logged.'))
versions=[]
for row in read(str((S/'fresh-retrievals.json').relative_to(R))):
 t=(R/row['path']).read_text(); versions.append(dict(path=row['path'],url=row['request_url'],title=re.findall(r'<meta name="citation_title" content="([^"]+)',t),versions=sorted(set(re.findall(r'\[v(\d+)\]',t))),hal_version='hal-05616391v1' if 'hal-05616391v1' in t else None,status=row['status']))
write('versions.json',versions)
write('audit-verdicts.json',{'scope':'Independent audit of I34 entropic claims actually reused, not all I34 geometry and not stipulated upstream truth','PASS':['half-squared-cost and relative/counting shift','DNWP target stability constant 1+2RL/epsilon','measurable-density conditional variance bound 2CLP_K epsilon','split-center variance/bias distinction','two-atom leakage bound and exact logistic threshold','fixed smooth finite-configuration coarea limsup','coincident-cluster counting-intercept obstruction and order of limits','conditional UB-to-Q approximation argument'],'repairs':[],'GAP':['uniform onset of fixed-configuration limit','general true entropic squared bias UB','transverse redistribution TR','original density-robust target-uniform Q']})
write('provenance-notes.json',{'scope':'I35 assigned report and source/experiment directories only','first_web_search':'Executed and read but not serialized; search.json retains the second exact request and response. No substituted response claimed.','primary_failures':'Earlier DNWP publication 403 and BK nonpaper response retained unchanged by dependency and response hashes; no new successful publication retrieval claimed.','corpus':'Entire corpus checked read-only; no full cache copies. Nine BT texts are stipulated premises.','numerics':'No floating quadrature or Sinkhorn solver used. Exact rational algebra models are labelled separately from true continuous Gibbs examples.','status':'UB/Q unproved and not refuted; transport parked pending TR; no nomination/count/priority claim.'})
print(json.dumps({'dependencies':len(deps),'contracts':len(contracts),'read_passages':len(log),'reused_primary':len(primary),'manuscripts':len(manuscripts),'catalogue_entries':len(links)},indent=2))
