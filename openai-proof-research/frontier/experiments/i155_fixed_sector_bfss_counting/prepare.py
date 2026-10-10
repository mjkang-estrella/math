"""Author-only evidence assembly. Reuses existing flat maps; no corpus traversal/copy."""
from pathlib import Path
import json,hashlib,re,difflib
S=Path('frontier/sources/i155_fixed_sector_bfss_counting')
X=Path('frontier/experiments/i155_fixed_sector_bfss_counting')
OLD=Path('frontier/sources/i153_many_body_spectral_discovery')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_bytes())
def save(p,x):Path(p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p,known=None):
 p=str(p)
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:151|154)(?:[-_/])',p)
 if p.startswith(str(S)+'/') or p.startswith(str(X)+'/'):return
 assert p not in MUTABLE
 r=known or row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json')+[dict(source=str(OLD),experiment='frontier/experiments/i153_many_body_spectral_discovery',report='frontier/iterations/i153-many-body-spectral-discovery.md',seal=row(OLD/'seal.json'))]
for pack in packs:
 add(pack['seal']['path'],pack['seal'])
 for r in load(pack['seal']['path'])['files']:add(r['path'],r)
for c in load(S/'contexts.json'):
 for key in ['raw','snapshot','brief','other','decoded']:
  if key in c:add(c[key])
for r in load(S/'snapshots.json'):
 if r['path'] not in MUTABLE:add(r['path'])
conversation=[row('frontier/iterations/i153-many-body-spectral-discovery.md'),row('frontier/experiments/i153-parent-verification.json')]
for r in conversation:
 add(r['path'],r);r['reading']='Complete report/finalized parent response supplied in user message; not fabricated tool-display coverage.'
save(S/'conversation-reading.json',conversation)
reads=load(S/'read-manifest.json');coverage={}
for r in reads:
 add(r['path'])
 if r['status']=='supplied-and-read':coverage.setdefault(r['path'],[]).append([r['start'],r['end']])
def merged(v):
 out=[]
 for a,b in sorted(v):
  if out and a<=out[-1][1]:out[-1][1]=max(out[-1][1],b)
  else:out.append([a,b])
 return out
cv=[]
for p,v in sorted(coverage.items()):
 t=Path(p).read_text();z=merged(v);cv.append(dict(path=p,ranges=z,characters=len(t),full=z==[[0,len(t)]]))
save(S/'coverage.json',cv)
cm={r['path']:r for r in cv};diffs=load(S/'thermal-diff-map.json')
full_diff=cm[str(S/'thermal-diff-view.txt')]['full'];assert full_diff
for d in diffs:
 add(d['base']);add(d['target']);assert cm[d['base']]['full']
bose=[]
for r in load(S/'bose-reading-plan.json'):
 p=r['path'];add(p)
 direct=cm.get(p,{}).get('full',False)
 via_diff=any(d['target']==p for d in diffs)
 bose.append(dict(**r,covered=direct or via_diff,method='complete direct supplied ranges' if direct else 'read base equal runs plus fully read contextual changes' if via_diff else 'not fully supplied'))
save(S/'bose-coverage.json',bose)
source=sorted({r['path'] for r in reads if r['path'].endswith(('.tex','.txt')) and ('/external/' in r['path'] or '/corpus/' in r['path'] or '/outside/' in r['path'])}|{d['target'] for d in diffs})
pattern=r'Weyl|Poincar.{0,2}|singular|stabili[sz]\w*|multiplicit\w*|fermion\w*|gauge|domain|covarian\w*|Palm|route\w*|count\w*|channel\w*|Born.{0,3}Oppenheimer'
rx=re.compile(pattern,re.I);out=[]
for p in source:
 add(p);t=Path(p).read_text();offset=0
 for no,line in enumerate(t.splitlines(keepends=True),1):
  for m in rx.finditer(line):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group()))
  offset+=len(line)
save(S/'lexical-query.json',dict(paths=source,pattern=pattern,flags='IGNORECASE',positions='Zero-based half-open Unicode character positions; one-based splitlines. No normalization, stemming or deduplication. Search is not reading.'))
save(S/'lexical-occurrences.json',out)
bindings=[]
for r in load(S/'http-log.json'):
 if 'failure' in r:continue
 p=S/'external'/(r['key']+'.pdf');t=p.with_suffix('.txt')
 bindings.append(dict(pdf=row(p),text=row(t),url=r['url'],extraction=['pdftotext','-layout',str(p),str(t)],scope='New extraction once; existing corpus bindings never regenerated.'))
save(S/'new-bindings.json',bindings)
if (S/'overlap-query.json').exists():
 for p in load(S/'overlap-query.json')['paths']:add(p)
save(S/'references.json',sorted(refs.values(),key=lambda r:r['path']))
save(S/'inherited-packages.json',packs)
print(json.dumps(dict(references=len(refs),packages=len(packs),read_records=len(reads),bose_files=len(bose),bose_uncovered=[r['path'] for r in bose if not r['covered']],lexical_occurrences=len(out),new_bindings=len(bindings))))
