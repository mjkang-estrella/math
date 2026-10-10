"""Prepare declared evidence references, not a corpus traversal or a seal."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i151_spatial_dynamical_percolation_continuation'
OLD='frontier/sources/i149_spectral_stochastic_universality_discovery'
def read(p):return (ROOT/p).read_bytes()
def obj(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,d):(ROOT/p).write_text(json.dumps(d,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
flat={}
def add(p,h=None,size=None):
 if p.startswith(S+'/') or p.startswith('frontier/experiments/i151_spatial_dynamical_percolation_continuation/'):return
 if p in {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}:return
 assert not re.search(r'/(?:i|iteration)(147|148|150)[-_]',p),p
 assert (ROOT/p).is_file() and not (ROOT/p).is_symlink(),p
 if h is None:h=sha(read(p))
 d={'path':p,'sha256':h,'bytes':(ROOT/p).stat().st_size if size is None else size}
 if p in flat:assert flat[p]==d,(p,flat[p],d)
 flat[p]=d
for r in obj(OLD+'/immutable-flat.json')['files']:add(r['path'],r['sha256'],r['bytes'])
add(OLD+'/immutable-flat.json')
se=obj(OLD+'/seal.json');add(OLD+'/seal.json')
for r in se['files']:add(r['path'],r['sha256'],r['bytes'])
add('frontier/iterations/iteration149-spectral-stochastic-universality-discovery-task.json','12378ffe25d5d800bc9d343ee5f58953ead19348267d78236f62197a24d2e150')
add('frontier/experiments/i149-parent-verification.json','763b12164ace79bb95b65a5a1d42bcdc0f6214ed494e4ede333be4506665b73d')
plans=[];passages=[]
for p in sorted((ROOT/S).glob('*reading*.json')):
 d=obj(str(p.relative_to(ROOT)))
 if isinstance(d,list):
  plans.append(str(p.relative_to(ROOT)))
  for r in d:
   assert r['read'] is True,(p,r)
   add(r['path'],r['sha256'])
   passages.append({**r,'plan':str(p.relative_to(ROOT))})
ctx=obj(S+'/context-reading-plan.json')
for r in ctx['files']:
 add(r['path'],r['sha256'])
 if r['path'].endswith('.decoded.txt'):
  p=r['path'].replace('.decoded.txt','.json');add(p)
  name=Path(p).name;orig='frontier/iterations/'+name
  if (ROOT/orig).is_file():add(orig)
for r in obj(S+'/recursive-context-validation.json'):
 add(r['path'],r['sha256']);add(r['snapshot'],r['sha256'])
# Binding referenced raw primary files too, without re-extraction.
for r in obj(S+'/retrievals.json'):
 for key in ('path','text_path'):
  if key in r and (ROOT/r[key]).is_file():add(r[key],r.get('sha256' if key=='path' else 'text_sha256'))
write(S+'/immutable-flat.json',{'files':[flat[p] for p in sorted(flat)],'scope':'flat immutable auxiliary references; corpus originals and all 776 PDF/text pairs use the existing complete map, not copies'})
write(S+'/reading-index.json',{'plans':plans,'passages':passages,'convention':'str.splitlines; one-based lines; passage LF join without appended LF; already-read identical context lines deduplicated only by exact text'})
# Exact lexical multisets on the declared semantically read scope, not whole corpus.
scope={}
for r in passages:scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
for r in ctx['files']:scope.setdefault(r['path'],set()).update(range(1,r['lines']+1))
expressions={'verdict':r'\b(?:PASS|FAIL|INCOMPLETE|unresolved)\b','spatial':r'\b(?:pivotal|quenched|localization|localisation|Poisson|clock|four.arm|interface)\b','audit':r'\b(?:H[oö]lder|Kelvin|harmonic|normal derivative|hierarch\w*|eigenvector\w*)\b'}
occ={k:[] for k in expressions}
coverage=[]
for p,ns in sorted(scope.items()):
 ls=read(p).decode().splitlines();ranges=[]
 for n in sorted(ns):
  if not ranges or n>ranges[-1][1]+1:ranges.append([n,n])
  else:ranges[-1][1]=n
  for key,rx in expressions.items():
   for m in re.finditer(rx,ls[n-1],re.I):occ[key].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group()})
 coverage.append({'path':p,'total_lines':len(ls),'covered_lines':len(ns),'ranges':ranges,'complete':len(ns)==len(ls),'sha256':sha(read(p))})
write(S+'/focused-lexical.json',{'expressions':expressions,'occurrences':occ,'counts':{k:len(v) for k,v in occ.items()},'position_convention':'Unicode code points, zero-based half-open columns; one-based splitlines; exact multiplicities across distinct paths retained'})
write(S+'/completion-coverage.json',{'files':coverage,'context_unique_lines':len(ctx['groups']),'context_line_occurrences':sum(r['lines'] for r in ctx['files']),'passages':len(passages),'reading_claim':'declared semantic readings and exact deduplication; byte checks alone do not establish reading'})
print(json.dumps({'flat_references':len(flat),'passages':len(passages),'files_with_reading_coverage':len(coverage),'lexical_counts':{k:len(v) for k,v in occ.items()}},sort_keys=True))
