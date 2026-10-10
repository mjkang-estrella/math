"""Author-side reference assembly; no copied corpus or ancestor execution."""
from pathlib import Path
import json,hashlib,re,bisect
S=Path('frontier/sources/i144_critical_siphon_window_repulsion');X=Path('frontier/experiments/i144_critical_siphon_window_repulsion');OLD=Path('frontier/sources/i141_intermittent_rate_permanence')
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_bytes())
def save(n,z):(S/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p):
 p=str(p)
 assert not re.search(r'(?:^|/)(?:i|iteration)(?:139|140|142|143)(?:[-_/])',p),p
 if p.startswith(str(S)+'/') or p.startswith(str(X)+'/'):return
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json')+[dict(source=str(OLD),experiment='frontier/experiments/i141_intermittent_rate_permanence',report='frontier/iterations/i141-intermittent-rate-permanence.md',seal=row(OLD/'seal.json'))]
for pack in packs:
 add(pack['seal']['path'])
 for r in load(pack['seal']['path'])['files']:add(r['path'])
for c in load(S/'contexts.json'):add(c['raw'])
for r in load(S/'snapshots.json'):
 if r['path'] not in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:add(r['path'])
add(load(S/'direct-context-binding.json')['task'])
reads=load(S/'read-manifest.json')
for r in reads:
 add(r['path']);t=Path(r['path']).read_text();a,b=r['char_start'],r['char_end'];starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 r.update(start_line=t[:a].count('\n')+1,end_line=t[:b].count('\n')+1,splitlines_start=bisect.bisect_right(starts,a),splitlines_end=bisect.bisect_right(starts,max(a,b-1)))
save('read-manifest.json',reads)
source=sorted(set(r['path'] for r in reads if r['path'].endswith('.tex') or '/external/' in r['path'] and r['path'].endswith('.txt')))
prior=sorted(set(load(OLD/'overlap-query.json')['files']+['frontier/iterations/i141-intermittent-rate-permanence.md']))
for label,files,pattern in [('source',source,r'persist\w*|perman\w*|siphon\w*|time[- ]depend\w*|time[- ]vary\w*|bounded kinetics|affine|active|cut|window\w*|Metzler|Perron|irreducib\w*'),('overlap',prior,r'persistently excit\w*|intermittent[- ]rate\w*|siphon\w*|mass[- ]action|P138|rank[- ]one.*perman\w*|endpoint[- ]label|transfer[- ]to[- ]branch')]:
 rx=re.compile(pattern,re.I);out=[]
 for p in files:
  add(p)
  for no,line in enumerate(Path(p).read_text(errors='replace').splitlines(),1):
   for m in rx.finditer(line):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),text=m.group(),line_text=line))
 save(label+'-query.json',dict(files=files,pattern=pattern,flags='IGNORECASE',convention='UTF8 replacement decoded splitlines; one-based line, zero-based half-open character offsets; exact repeated matches retained'))
 save(label+'-results.json',out)
save('references.json',sorted(refs.values(),key=lambda r:r['path']));save('inherited-packages.json',packs)
save('failure-log.json',[
 dict(kind='display-truncation',detail='Two initial I120 decoded displays from character 60000 through the ending were truncated. Both attempts are marked in read-manifest; smaller 60000:79000,79000:91000,91000:end reads recovered complete supplied coverage.'),
 dict(kind='unused-preparation',detail='Lossless deduplicated decoded-display.txt/decoded-nodes.json were prepared but not used to claim context reading. Actual complete decoded task views were read instead.'),
 dict(kind='retrieval-failure',detail='The 2025 Komatsu-Nakajima publisher full endpoint returned HTTP 403; the full failed HTML response is retained and hashed. Web DOI retrieval also returned Internal Error. Preview/search passages are not the full paper.'),
 dict(kind='coverage-limit',detail='Current ledgers/catalogue were frozen; selected relevant passages and endings were read, not all historical ledger prose. Literature search is bounded and not exhaustive; no full Craciun construction audit is claimed.'),
 dict(kind='inherited-failures',detail='Ancestor literal failures and receipts are retained by the flat reference union, including original endpoint-only R2 FAIL, truncated displays, publisher403, unavailable NumPy and uncertified RK4. No inherited program was rerun.'),
 dict(kind='mathematical-limit',detail='General P138 remains unresolved. First-order transfer criterion can fail; endpoint-label windows require coordinatewise endpoint growth control. Scalar rare-mass nondoubling does not supply it. No long-time exact counterexample found.')])
print(json.dumps(dict(flat_references=len(refs),inherited_packages=len(packs),read_records=len(reads),source_matches=len(load(S/'source-results.json')),overlap_matches=len(load(S/'overlap-results.json')))))
