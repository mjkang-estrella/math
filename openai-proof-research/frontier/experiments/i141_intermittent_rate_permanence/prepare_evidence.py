"""Author-side flat reference assembly. Does not run ancestor programs or copy corpus."""
from pathlib import Path
import json,hashlib,re
S=Path('frontier/sources/i141_intermittent_rate_permanence');X=Path('frontier/experiments/i141_intermittent_rate_permanence')
assert not (S/'seal.json').exists()
OLD=Path('frontier/sources/i138_nonlinear_dynamics_discovery')
def load(p):return json.loads(Path(p).read_bytes())
def save(n,j):(S/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p):
 p=str(p)
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:139|140)(?:[-_/])',p),p
 if p.startswith(str(S)+'/') or p.startswith(str(X)+'/'):return
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json');packs.append(dict(source=str(OLD),experiment='frontier/experiments/i138_nonlinear_dynamics_discovery',report='frontier/iterations/i138-nonlinear-dynamics-discovery.md',seal=row(OLD/'seal.json')))
for pack in packs:
 add(pack['seal']['path'])
 for r in load(pack['seal']['path'])['files']:add(r['path'])
for c in load(S/'contexts.json'):add(c['raw'])
for r in load(S/'read-manifest.json'):add(r['path'])
for r in load(S/'snapshots.json'):
 if r['path'] not in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:add(r['path'])
# Bounded lexical domains: selected source operations, new primary texts, and reports <=138 only.
base=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints')
roots=load(OLD/'family-roots.json')
source=sorted(str(p) for r in roots for p in (base/r/'build/sections').glob('*.tex'))
source+=sorted(str(p) for p in (S/'external').glob('*.txt'))
source=sorted(set(source))
prior=[]
for root in ['frontier/iterations','frontier/reviews']:
 for p in Path(root).glob('i*.md'):
  m=re.match(r'i(\d+)[-]',p.name)
  if m and int(m[1])<=138:prior.append(str(p))
for label,files,pattern in [('source',source,r'persist\w*|perman\w*|siphon\w*|time[- ]depend\w*|time[- ]vary\w*|bounded kinetics|affine|active|cut|window\w*'),('overlap',sorted(prior),r'persistently excit\w*|intermittent[- ]rate\w*|siphon\w*|mass[- ]action|P138|rank[- ]one.*perman\w*')]:
 rx=re.compile(pattern,re.I);matches=[]
 for p in files:
  add(p)
  for no,line in enumerate(Path(p).read_text(errors='replace').splitlines(),1):
   for m in rx.finditer(line):matches.append(dict(path=p,line=no,start=m.start(),end=m.end(),text=m.group(),line_text=line))
 save(label+'-query.json',dict(files=files,pattern=pattern,flags='IGNORECASE',convention='UTF8 replacement decoded splitlines; zero-based character match offsets'))
 save(label+'-results.json',matches)
save('inherited-packages.json',packs);save('references.json',sorted(refs.values(),key=lambda r:r['path']))
# Record versions from exact retained primary HTML, without claiming a conversion.
versions=[]
for f in sorted((S/'external').glob('*current.html')):
 t=f.read_text();a=t.index('Submission history');b=t.index('</div>',a);versions.append(dict(path=str(f),start=a,end=b,text=t[a:b],sha256=hashlib.sha256(t[a:b].encode()).hexdigest()))
save('current-versions.json',versions)
save('failure-log.json',[
 dict(kind='scope-error',detail='Initial find .. -name AGENTS.md listed unrelated sibling and active snapshot filenames. No contents opened, hashed or bound; no writes outside owned roots.'),
 dict(kind='display-truncation',detail='Initial 0:40000 I138 decoded brief display truncated; recovered 0:19500 and 19500:39000 plus existing 39000:68000. All mandatory contexts now have full supplied coverage.'),
 dict(kind='display-truncation',detail='Broad rg and ledger-excerpt outputs truncated. Retained ledger-excerpts are acquisition/search output only; read-manifest marks actual supplied scoped reads. Combined first web/source response truncated web portion; September introduction itself supplied through its ending.'),
 dict(kind='command-failure',detail='Reader path used i141_interment_rate_permanence instead of i141_intermittent_rate_permanence; exited unsuccessfully with stderr redirected. No data read.'),
 dict(kind='dependency-failure',detail='First switching simulation import numpy failed with ModuleNotFoundError. Actual run replaced it with pure-Python explicit RK4, step .02, no certified error bound.'),
 dict(kind='retrieval-failure',detail='Komatsu-Nakajima 2025 publisher full text returned HTTP 403 both web and urllib. Search abstract/introduction only; no full-proof comparison claimed.'),
 dict(kind='coverage-limit',detail='Exploratory web searches not all retained verbatim; two complete responses retained in web-search-retained.json. No exhaustive/current-full-literature claim.'),
 dict(kind='mathematical-limit',detail='General P138 unresolved; nonlinear averaged upper coefficients unbounded, critical siphon and label-change mechanism unpaid. Finite simulations do not resolve eventual compactness.')])
print(json.dumps({'flat_refs':len(refs),'packages':len(packs),'source_matches':len(load(S/'source-results.json')),'prior_matches':len(load(S/'overlap-results.json'))}))
