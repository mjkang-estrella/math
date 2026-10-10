"""One-shot I69 capture; writes only assigned I69 directories."""
import pathlib,json,hashlib,subprocess,shutil,datetime
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i69_global_algebra_rounding_budget'; O=R/'frontier/sources/i65_linked_symmetric_algebra_rounding'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
assert not (S/'inputs.json').exists()
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md']+mutable
paths += [str(p.relative_to(R)) for pat in ['frontier/iterations/i53-*.md','frontier/iterations/i59-*.md','frontier/iterations/i61-*.md','frontier/iterations/i65-*.md','frontier/reviews/i55-*.md','frontier/reviews/i56-*.md','frontier/reviews/i63-*.md','frontier/reviews/i64-*.md','frontier/findings/R014-*.md'] for p in R.glob(pat)]
paths += ['frontier/iterations/iteration69-global-algebra-rounding-budget-task.json','frontier/experiments/i65-parent-verification.json']
inputs=[]
for name in paths:
 b=(R/name).read_bytes();p=S/'inputs'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);inputs.append(dict(path=name,sha256=sha(b),mutable=name in mutable))
save(S/'inputs.json',inputs)
prior={x['path']:x['sha256'] for x in json.loads((O/'prior-hashes.json').read_text())}
for base in [O,R/'frontier/experiments/i65_linked_symmetric_algebra_rounding']:
 for p in base.rglob('*'):
  if p.is_file():prior[str(p.relative_to(R))]=sha(p.read_bytes())
save(S/'prior-hashes.json',[dict(path=p,sha256=h) for p,h in sorted(prior.items())])
for name in ['corpus.json','tree-outside-corpus.json','pins.json']:shutil.copyfile(O/name,S/name)
# Pins are references, not recursive archival copies.
pins=json.loads((S/'pins.json').read_text())
for x in pins:x['local_path']=str((O/'pinned'/x['path']).relative_to(R))
save(S/'pins.json',pins)
cp='frontier/sources/i14_spectral_width_novelty_r3/corpus'
searches=[]
for name,pattern in [('rounding',r'(?i)associativ.{0,40}(stabil|approxim)|orthogonal.{0,20}decompos|simplicial algebra'),('norms',r'(?i)cb.norm|completely bounded.{0,25}(small|norm)|Haagerup|conditional expectation'),('budget',r'(?i)deflation|mixed.mass|nonassociativ|near.square|dephasing')]:
 p=subprocess.run(['rg','--no-ignore','-n',pattern,cp],cwd=R,capture_output=True,text=True)
 lines=sorted(p.stdout.splitlines());save(S/(name+'-search.json'),lines)
 searches.append(dict(name=name,pattern=pattern,count=len(lines),returncode=p.returncode,stderr=p.stderr))
save(S/'searches.json',searches)
save(S/'capture-metadata.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='I69 only; old evidence referenced without recursive copying',initial_discovery_limit='First web search displayed but not separately archived; a second bounded search is archived. No theorem relies on the first display.'))
print(json.dumps(dict(inputs=len(inputs),prior=len(prior),searches={x['name']:x['count'] for x in searches})))
