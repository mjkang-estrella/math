"""Assemble I158's honest coverage and exact lexical records; author phase only."""
from pathlib import Path
import json,hashlib,re
S=Path('frontier/sources/i158_fixed_sector_bfss_counting_r2')
A=Path('frontier/sources/i155_fixed_sector_bfss_counting')
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
reads=load(S/'read-manifest.json')
for i,r in enumerate(reads):
 r['status']='truncated-display-not-full-reading' if i in {8,9} else 'supplied-and-read'
save(S/'read-manifest.json',reads)
coverage={}
for r in reads:
 if r['status']=='supplied-and-read':coverage.setdefault(r['path'],[]).append([r['start'],r['end']])
def merge(ranges):
 out=[]
 for a,b in sorted(ranges):
  if out and a<=out[-1][1]:out[-1][1]=max(b,out[-1][1])
  else:out.append([a,b])
 return out
cv=[]
for p,rs in sorted(coverage.items()):
 t=Path(p).read_text();rs=merge(rs);cv.append(dict(path=p,ranges=rs,characters=len(t),full=rs==[[0,len(t)]]))
save(S/'coverage.json',cv)
conversation=[dict(**row('frontier/iterations/i155-fixed-sector-bfss-counting.md'),reading='Complete original supplied in user message; semantic reading of conversation, not invented file-display coverage.'),dict(**row('frontier/experiments/i155-parent-verification.json'),reading='Finalized parent response supplied in user message; selective parent checks are not universal proof.')]
save(S/'conversation-reading.json',conversation)
save(S/'failure-log.json',[
 dict(attempt='Combined context.py/catalogue/first 40000 I155 brief characters display',result='Outer tool output truncated; not a complete semantic receipt.',recovery='I155 decoded-new-view.txt and i155-reused-view.txt plus scalar-view.txt read in bounded complete calls.'),
 dict(attempt='Initial combined line statistics and full BFSS source display',result='Outer tool output truncated, including middle of source.',recovery='BFSS source recovered completely in receipts 1 and 2.'),
 dict(attempt='Three base-context reading ranges, 30000..120000, in one functions call',result='Receipt 7 supplied; receipt 8 truncated and receipt 9 omitted by output wrapper.',recovery='No full recovery of receipts 8 and 9 claimed; recursive reading remains incomplete.'),
 dict(attempt='Inherited acquisition failures',result='I155 and earlier failure logs remain immutable references; no ancestor retrieval or extraction rerun.',recovery=None)
])
save(S/'pending-obligations.json',dict(complete_requested_review=False,overall_verdict='UNRESOLVED',narrow_mathematical_verdict='PASS without substantive repairs for S155 sections 3.1-3.7 relative to stipulated BFSS inputs and ordinary FNT',obligations=[
 'Read all remaining ranges of the 798775-character recursive base view, including recovery of truncated attempts; do not infer reading from decoding or hashes.',
 'Complete semantic inspection of all recursive structured/embedded task fields, finalized original responses and objections; retain exact occurrences.',
 'Independently complete the required Bose source/companion comparison coverage; I155 closure remains new I155 work and B153 stays parked.',
 'Finish fresh operative comparator reading where required, beyond complete FNT and DFS sections 3.3 through ending; inherited I155 comparisons are not I158 fresh readings.',
 'A later contribution gate remains necessary even after the complete correctness gate is discharged.'
],repairs=[],acceptance_decision=False))
paths=sorted({r['path'] for r in reads if '/outside/' in r['path'] or '/external/' in r['path']}|{'frontier/iterations/i155-fixed-sector-bfss-counting.md'})
pattern=r'Weyl|Poincar.{0,2}|stabili[sz]\w*|multiplicit\w*|fermion\w*|gauge|domain|Born.{0,3}Oppenheimer|Neumann|Dirichlet|spin\(\d+\)'
q=dict(paths=paths,pattern=pattern,flags='IGNORECASE',positions='one-based splitlines; zero-based half-open Unicode character positions; no normalization; search does not imply full reading')
out=[];rx=re.compile(pattern,re.I)
for p in paths:
 off=0
 for no,line in enumerate(Path(p).read_text().splitlines(keepends=True),1):
  for m in rx.finditer(line):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=off+m.start(),absolute_end=off+m.end(),text=m.group()))
  off+=len(line)
save(S/'lexical-query.json',q);save(S/'lexical-occurrences.json',out)
refs={r['path']:r for r in load(S/'references.json')}
for p in set(paths)|{r['path'] for r in reads}|{r['path'] for r in conversation}:
 if p.startswith(str(S)+'/'):continue
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
save(S/'references.json',sorted(refs.values(),key=lambda r:r['path']))
save(S/'snapshots.json',load(A/'snapshots.json'))
print(json.dumps(dict(read_records=len(reads),complete_fresh_files=sum(x['full'] for x in cv),lexical_occurrences=len(out),references=len(refs),complete_requested_review=False)))
