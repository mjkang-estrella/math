"""Record exact dependencies/read ranges and inventory checks; no corpus copies."""
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i33_density_robust_brenier'
CROOT=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
CM=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,data):(S/name).write_text(json.dumps(data,indent=2)+'\n')
def record(p):
 b=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'sha256':sha(b),'bytes':len(b)}

def main():
 cm=json.loads(CM.read_text());tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text())
 bt='Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026'
 entropy='A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/build/manuscript/transport.tex'
 selected=[r for r in cm['files'] if bt in r['path'] or entropy in r['path']]
 write('source-manifest.json',selected)
 write('dependency-manifest.json',[record(CM)])
 inventory=[r['path'] for r in tree['tree'] if r['type']=='tree' and r['path'].count('/')==1]
 assert len(inventory)==749 and not tree['truncated']
 hits=[]
 for row in cm['files']:
  p=CROOT/row['path']
  if p.suffix not in ('.tex','.md'):continue
  data=p.read_text()
  matches=[i for i,l in enumerate(data.splitlines(),1) if re.search('Brenier|brenier',l)]
  if matches:hits.append({'path':row['path'],'lines':matches})
 write('inventory-screen.json',{'inventory_count':len(inventory),'tree_entries':len(tree['tree']),'corpus_count':len(cm['files']),'title_pattern':'transport|Brenier|Wasserstein|Monge','title_matches':[p for p in inventory if re.search('transport|Brenier|Wasserstein|Monge',p,re.I)],'text_pattern':'Brenier|brenier','text_hits':hits,'scope':'inventory and text search, not semantic reading of every source','BT_companions':'one BT manuscript in complete inventory; all nine text files read','entropy_screen':'only its initial smooth strongly log-concave hypotheses used; no result imported'})
 passages=[]
 def read(p,a,b,note):
  p=ROOT/p if isinstance(p,str) else p;ls=p.read_bytes().splitlines(keepends=True)
  assert 1<=a<=b<=len(ls),(p,a,b,len(ls))
  data=b''.join(ls[a-1:b]);passages.append({'path':str(p.relative_to(ROOT)),'start_line':a,'end_line':b,'sha256':sha(data),'note':note})
 for row in selected:
  p=CROOT/row['path'];end=len(p.read_bytes().splitlines())
  read(p,1,24 if entropy in row['path'] else end,'Full BT text read' if bt in row['path'] else 'Hypothesis screen only')
 for p in ['AGENTS.md','frontier/TEN-FINDINGS.md','frontier/iterations/iteration32-geometric-relativity-discovery-task.json','frontier/iterations/i32-geometric-relativity-discovery.md']:
  f=S/'inputs'/p;read(f,1,len(f.read_bytes().splitlines()),'Obligatory frozen input; long inputs read in overlapping chunks')
 lit=S/'literature'
 ranges={
 'lm-v3.txt':[(452,625,'Theorem 2.1, Proposition 2.2, and complete proof')],
 'ruan-v1.txt':[(90,230,'Error definitions and theorem overview'),(1456,1592,'Repair construction and gap proof'),(1700,1745,'Theorem 8 and proof')],
 'wang-v1.txt':[(1,200,'Main assumptions and precise exponents'),(306,528,'Moreau cancellation, coercivity, repair and Theorem 1 proof'),(646,750,'Sharpness source geometry and target construction')],
 'merigot-v1.txt':[(275,635,'Divergence, map stability and plan-conditioning proofs'),(638,714,'Entropic bias route and its scope')],
 'dnwp-v1.txt':[(748,835,'Bias hypotheses, constants, and cube-root proof')],
 'ford-v1.txt':[(1,170,'Assumptions and statements'),(940,982,'Theorem 4.6 and proof'),(1130,1255,'Sharpness construction: non-full source support')],
 'bk-v2.txt':[(100,180,'Exact hypotheses and Theorem 1.3'),(370,460,'Acyclicity lemma and proof'),(740,778,'Transfer to fixed prescribed masses')],
 'bk-nsf.txt':[(1,90,'Successful published-byte identity/title check; not full proof read')],
 'letunstable.txt':[(1,213,'Theorem hypotheses and conjecture context')],
 }
 # The unversioned HAL bytes and the pinned v1 bytes coincide.
 assert (lit/'merigot.pdf').read_bytes()==(lit/'merigot-v1.pdf').read_bytes()
 assert (lit/'merigot.txt').read_bytes()==(lit/'merigot-v1.txt').read_bytes()
 # Early LM/Ruan passages were read in I32's retained extraction; freshly retrieved bytes coincide.
 for new,old in [('lm-v3.txt','2411.04908v3.txt'),('ruan-v1.txt','2610.07577v1.txt')]:
  assert (lit/new).read_bytes()==(ROOT/'frontier/sources/i32_geometric_relativity_discovery/literature'/old).read_bytes()
 for name,rr in ranges.items():
  for a,b,note in rr:read(lit/name,a,b,note)
 versions=[]
 for name in ['lm-current.html','ruan-current.html','wang-current.html','ford-current.html','dnwp-current.html','bk-current.html']:
  p=lit/name;ls=p.read_text().splitlines();a=next(i for i,l in enumerate(ls,1) if 'class="submission-history"' in l);b=next(i for i in range(a,len(ls)+1) if '</div>' in ls[i-1]);read(p,a,b,'Fresh primary submission history')
  versions.append({'path':str(p.relative_to(ROOT)),'history_text':'\n'.join(ls[a-1:b]),'sha256':sha(p.read_bytes())})
 write('versions.json',versions)
 write('read-passages.json',passages)
 contracts=[]
 labels={
 'sections/cells.tex':('cells:calculus; cells:weights','uniform-source proof premises; smooth positive weighting reuses dominated convergence, connectivity and dual minimization'),
 'sections/moments.tex':('moments:midpoint; moments:derivative','uniform density only; exact factor-one domination; coefficient 162; configuration-local perturbation threshold'),
 'sections/finite_stability.tex':('finite:potentials','fixed masses, range inversion without a q bound, interior noncollision for optimal target coupling, endpoint merging'),
 'sections/gradient.tex':('gradient:interpolation; gradient:extension','convex interpolation and finite approximation; no density-weighted moment assertion'),
 'sections/sharpness.tex':('cells:optimality; sharpness:exponent','unique finite-map optimality and three-atom W2 exponent obstruction'),
 }
 for row in selected:
  for suffix,(label,scope) in labels.items():
   if row['path'].endswith(suffix):contracts.append({'kind':'stipulated-source','path':str((CROOT/row['path']).relative_to(ROOT)),'sha256':row['sha256'],'labels':label,'scope':scope})
 pc=[('lm-v3.txt','Theorem 2.1 / Proposition 2.2','variance, comparability, interpolation; no moment-inverse claim'),('ruan-v1.txt','Section 11 / Theorem 8','repair gap O(W1) or O(W2); L2 map W1^(1/4) at bounded density'),('wang-v1.txt','Theorem 1; Lemmas 6-8','compensated error O(t^2) with bounded weight; map W2^(1/4); disconnected unbounded sharpness source'),('merigot-v1.txt','Theorems 2.2, 3.1, 3.4, 4.3','fourth-power coercivity, squared map error sqrt gap, configuration-dependent semi-discrete bias'),('ford-v1.txt','Theorem 4.6 / Proposition 5.2','W1 map bound and upper-regular sharpness without positive density on convex hull'),('dnwp-v1.txt','Proposition 4.1 / Theorem 4.3','entropic bias and W2 cube root with configuration-dependent constants; published PDF retrieval blocked'),('bk-v2.txt','Theorem 1.3 / Lemma 2.1','acyclic transfer graph; atom-count-dependent mass reassignment')]
 for name,label,scope in pc:contracts.append({'kind':'primary-proof','labels':label,'scope':scope,**record(lit/name)})
 write('contracts.json',contracts)
 write('provenance-notes.json',{'first_exploratory_web_response':'not serialized; later two query/response objects retained; no completeness claim for first response bytes','published_fetches':{'bk-published.pdf':'HTTP 200 but HTML challenge, not a PDF; arXiv v2 and NSF PDF succeeded','dnwp-published.pdf':'HTTP 403 retained; v1 author manuscript read'},'no_agents':True,'no_shared_index_edits':True,'no_staging_commits_or_pushes':True,'semantic_scope':'Read log distinguishes full BT proof reads, selected primary proofs, and hypothesis-only screens','initial_cwd_error':'One read-only shell call omitted workdir and returned missing-file errors; repeated in correct project directory','full_followup_brief':'followup-brief.txt; original I32 JSON and full report frozen without edits'})
 print(json.dumps({'selected_sources':len(selected),'contracts':len(contracts),'read_passages':len(passages),'inventory':len(inventory),'corpus':len(cm['files'])}))

if __name__=='__main__':main()
