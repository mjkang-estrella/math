from pathlib import Path
import json,hashlib,shutil,datetime
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i60_threshold_structural_combinatorics_discovery'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
if (S/'inputs.json').exists():raise SystemExit('Frozen inputs already exist; refusing to refresh.')
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/README.md','README.md','frontier/iterations/README.md','frontier/iterations/i13-fresh-discovery.md','frontier/iterations/i19-fresh-structural-discovery.md','frontier/iterations/i22-combinatorial-discovery.md','frontier/iterations/i25-matching-entropy-improvement-resumed.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md','frontier/reviews/i58-standard-map-additive-entropy-novelty.md']
mutable=set(inputs[4:8]); rows=[]
for p in inputs:
 b=(ROOT/p).read_bytes(); dest=S/'inputs'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 rows.append(dict(path=p,frozen=str(dest.relative_to(ROOT)),sha256=sha(b),mutable=p in mutable))
(S/'inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); by={x['path']:x for x in tree['tree'] if x['type']=='blob'}
corpus=[]
for p in sorted(C.rglob('*')):
 if p.is_file():
  rel=str(p.relative_to(C));b=p.read_bytes();assert blob(b)==by[rel]['sha'],rel
  corpus.append(dict(path=rel,sha256=sha(b),git_blob=blob(b),bytes=len(b)))
(S/'corpus-inventory.json').write_text(json.dumps(dict(pin=PIN,tree_entries=len(tree['tree']),manuscripts=len({x['path'].split('/')[1] for x in tree['tree']}),files=corpus),indent=2)+'\n')
selected=['A-uniform-influence-bound-for-hypergraph-properties-October-5-2026','A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026','Graph-Decompositions-at-the-Integral-Expectation-Threshold-October-5-2026','Talagrands-discrete-convexity-conjecture-September-23-2026','Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026']
manifest=[]
for row in corpus:
 if row['path'].split('/')[1] in selected:
  dest=S/'pinned'/row['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((C/row['path']).read_bytes())
  manifest.append(dict(**row,frozen=str(dest.relative_to(ROOT)),url=f'https://raw.githubusercontent.com/openai/math/{PIN}/'+row['path']))
(S/'pinned-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Prior screen scope is an explicit frozen list, never a growing report glob.
terms=['slice','threshold','convexity','influence','Hall','root','matching','prophet']
search=[]
for row in rows:
 if '/iterations/i' not in row['path']:continue
 for i,line in enumerate((ROOT/row['frozen']).read_text().splitlines(),1):
  for term in terms:
   if term.lower() in line.lower():search.append([row['path'],i,term,line])
(S/'prior-screen-lines.json').write_text(json.dumps(sorted(search),indent=2)+'\n')
print(json.dumps(dict(inputs=len(rows),corpus=len(corpus),selected=len(manifest))))
