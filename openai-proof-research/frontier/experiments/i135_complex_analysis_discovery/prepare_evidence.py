"""Author-side preparation; never invoked by offline replay. Writes only I135 paths."""
import hashlib,json,re
from pathlib import Path
S=Path('frontier/sources/i135_complex_analysis_discovery');X=Path('frontier/experiments/i135_complex_analysis_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def row(p):b=Path(p).read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
assert not (S/'seal.json').exists()
snaps=json.loads((S/'snapshots.json').read_text())
p=Path('frontier/iterations/iteration135-complex-analysis-discovery-task.json'); dest=S/'snapshots'/p
if not dest.exists():dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes());snaps.append(dict(**row(p),snapshot=str(dest)))
put(S/'snapshots.json',sorted(snaps,key=lambda r:r['path']))
# These short non-brief fields were supplied completely in the research session.
m=json.loads((S/'read-manifest.json').read_text())
for p in sorted((S/'decoded').glob('*other.json')):
 if not any(r['path']==str(p) for r in m):
  b=p.read_bytes();ls=b.decode().splitlines();m.append(dict(path=str(p),sha256=sha(b),field=None,start=1,end=len(ls),total=len(ls),range_sha256=sha('\n'.join(ls).encode()),raw_lf=b.count(b'\n'),terminal_lf=b.endswith(b'\n'),recorded_after_actual_display=True))
put(S/'read-manifest.json',m)
selected=json.loads((S/'selected-inventory.json').read_text())
files=[]
for p in Path('frontier/iterations').glob('*.md'):
 match=re.match(r'i(\d+)[-_]',p.name)
 if match and int(match[1])<=132:files.append(str(p))
files+=['frontier/scouts/analysis.md']
queries={'overlap':dict(files=sorted(set(files)),pattern=r'Brennan|Koebe|Littlewood|ultraflat|circle[- ]domain|conformal remov|inverse[- ]square|schlicht',flags='IGNORECASE'), 'source':dict(files=sorted(set(r['local'] for r in selected)),pattern=r'endpoint|uniform|rigid|removab|retained|compatib|logarith|Littlewood|Brennan|Koebe|ultraflat|corank|prefactor',flags='IGNORECASE')}
for label,q in queries.items():
 out=[];pat=re.compile(q['pattern'],re.I)
 for p in q['files']:
  for n,l in enumerate(Path(p).read_text().splitlines(),1):
   for mt in pat.finditer(l):out.append(dict(path=p,line=n,start=mt.start(),end=mt.end(),text=mt.group(),line_text=l))
 put(S/(label+'-query.json'),q);put(S/(label+'-results.json'),out)
paths={r['path'] for r in m if not r['path'].startswith(str(S)+'/')}
paths.update(queries['overlap']['files'])
paths.update(['frontier/experiments/i132_discrete_probability_discovery/verify.py','frontier/experiments/i123_thermal_production_stability/verify.py','frontier/experiments/i114_quantum_information_discovery/html_text.py','frontier/sources/i114_quantum_information_discovery/search-domain.json'])
put(S/'references.json',[row(p) for p in sorted(paths)])
views=[]
for r in json.loads((S/'http-log.json').read_text()):
 p=Path(r['path']);views.append(dict(url=r['url'],html=row(p),text=row(p.with_suffix('.txt')),converter='frontier/experiments/i114_quantum_information_discovery/html_text.py',convention='UTF-8 deterministic block/text/math HTML view; splitlines and LF counts bound by read manifest'))
put(S/'html-bindings.json',views)
put(S/'failure-log.json',dict(scope='Acquisition/display limitations; not universal proof evidence',records=[
 dict(kind='truncated-display',source='task132 decoded brief',requested=[199,500],recovery=[333,363],note='Long embedded JSON stdout line; original bytes retained and affected range resupplied'),
 dict(kind='truncated-display',source='external/rigidity-v1.txt',requested=[1,308],recovery=[55,110]),
 dict(kind='truncated-display',source='i07-analysis.md',requested=[1,284],recovery=[[82,115],[110,215]]),
 dict(kind='truncated-display',source='i36-harmonic-analysis-discovery.md',requested=[260,366],recovery=[293,331]),
 dict(kind='lead-only-inventory',note='Two broad filename inventory calls listed active I133/I134/I136 AGENTS snapshot filenames. No contents of those outputs read, hashed, or bound; all selected output domains exclude them.'),
 dict(kind='failed-web-open',url='https://arxiv.org/html/2504.19336v2',error='404; metadata has only v1, which was acquired and read'),
 dict(kind='superseded-web-lead',url='https://arxiv.org/html/2512.09330v1',note='Exploratory older version not selected; current v13 June 5 2026 acquired and proof ending read'),
 dict(kind='unretained-exploratory-web-leads',note='Search results and web PDF rendering of Smith-Volberg ConfMap4_2011.pdf were exploratory only; no selected theorem depends on them. No fresh PDF extraction performed.'),
 dict(kind='scoped-reading',note='Ledger/scout/prior-report excerpts, source abstract/title searches, and selected proof ranges are not whole-file semantic reading. Exact selected source inventory includes unread representations, not a claim all 115 proofs were read.'),
 dict(kind='read-conventions',note='Reader records requested inclusive UTF-8 splitlines ranges; explicit recovery entries above qualify tool-display truncation. Decoded brief .txt appends one LF to the JSON string; raw LF counts and terminal LF are separately recorded. Range hashes join splitlines by LF without an appended newline.')]))
print(json.dumps(dict(reads=len(m),references=len(paths),lexical={k:len(json.loads((S/(k+'-results.json')).read_text())) for k in queries})))
