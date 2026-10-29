from pathlib import Path
import json,hashlib,datetime,sys,re,gzip,subprocess
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
if sys.argv[1]=='aliases':
 p=re.compile(rb'2180639[78]|Achour|degree.spread|2610[.]22142|Dawkins|Nappo|Zimbizi|minimum maximal matchings in permutahedra|2502[.]09968|Brenner.{0,50}Fink',re.I)
 roles=re.compile(r'(?:^|/)(?:SUMMARY|discovery|PROOF|review|DECISION)[^/]*\.(?:md|txt)$',re.I)
 echoes=re.compile(r'/(?:extracted[^/]*|rebuild[^/]*|replay[^/]*|packet|inputs|evidence|history|review-core|core|source-copy|verification)/',re.I)
 old=L.parent/'sol-fresh-source-discovery-r133/history-aliases.jsonl.gz';paths=set()
 with gzip.open(old,'rt') as f:
  for line in f:
   h,s=json.loads(line)
   if roles.search(s) and not echoes.search(s):paths.add(s)
 for s in subprocess.check_output(['rg','--files',str(R),'-g','*.md','-g','*.txt'],text=True).splitlines():
  s=str(Path(s).relative_to(R))
  if roles.search(s) and not echoes.search(s):paths.add(s)
 seen=set();hits=[];drift=[];n=0
 for s in sorted(paths):
  f=R/s
  if L in f.parents:continue
  if not f.exists() or f.stat().st_size>12000000:drift.append(s);continue
  b=f.read_bytes();h=sha(b);n+=1
  if h in seen:continue
  seen.add(h)
  if p.search(b):hits.append(dict(path=s,sha256=h,aliases=[m.group().decode(errors='replace') for m in p.finditer(b)]))
 dump('final-alias-receipt.json',dict(utc=utc(),pattern=p.pattern.decode(),complete_report_paths=n,distinct_bodies=len(seen),hits=hits,missing_or_oversized=drift,global_cutoff=None,scope='original named report roles, generated echo exclusions as retained; not every source/code or semantic absence'))
 print('final aliases',n,len(seen),'hits',len(hits),hits)
elif sys.argv[1]=='finalize':
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 rec=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 retained=[]
 for n in (133,135,137):
  d=L.parent/f'sol-fresh-source-discovery-r{n}'
  for name in ('history-receipt.json','registry-delta-receipt.json','registry-delta.json'):
   p=d/name
   if p.exists():retained.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
 dump('provenance.json',dict(created_utc=utc(),status='ZERO: ordinary source refutation excluded as routine corona consequence',credits=0,counts_unchanged=dict(additional=9,total=39,next=40),source_attribution=dict(author='Hassine Achour',title='A Degree-Spread Bound Between Independent Domination and Minimum Maximal Matchings: A Conjecture',concept_doi='10.5281/zenodo.21806397',version_doi='10.5281/zenodo.21806398',version='1.0.0',source='sources/paper.tex',label='conj:main'),http=rec,guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,limitations='sampled group RSS; unsampled transients not ruled out',environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')),retained=retained,search_queries=['2610.22142','Wild number conjecture spanning trees','wild number Dawkins proof conjecture','Achour degree-spread counterexample','A Degree-Spread Bound zenodo','corona saturation number matching','corona independent domination edge domination'],search_limits='public tool queries; no individual search-response hashes or exact query UTC available; fetched source bytes carry exact actual UTC; no worldwide priority claim',failures=[dict(operation='initial HTML extraction',error='ModuleNotFoundError bs4',exit=1,sampled_peak_group_rss=27516928),dict(operation='Wiley2022 web source',error='403 Forbidden'),dict(operation='SemanticScholar PDF',status=202,bytes=0),dict(operation='guessed AFTD URL',error='404'),dict(operation='Omega fixed delta',error='300-file cap reached')],registry_clearance=False,independent_review=False,lean=False,paper=False,external_mutations=False))
 freeze={}
 for p in sorted((L/'sources').iterdir()):
  if p.is_file():freeze[str(p.relative_to(L))]=dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
 for n in ('PROOF.md','checks.py','check-results.json','history-receipt.json','final-alias-receipt.json','registry-delta-receipt.json','original-reopen-receipts.json'):
  p=L/n;freeze[n]=dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
 dump('scientific-freeze.json',dict(utc=utc(),entries=freeze,mutable_NEXT_separate=True,source_question_resolved_in_ordinary_math=True,discovery_eligible=False))
 entries={str(p.relative_to(L)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ('finalmanifest.json','manifest-verification.json')}
 dump('finalmanifest.json',dict(utc=utc(),entries=entries,exclusions=['finalmanifest.json: self','manifest-verification.json: verification receipt']))
 print('finalmanifest',len(entries),'entries')
elif sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_bytes());bad=[]
 for n,r in j['entries'].items():
  p=L/n
  if not p.is_file() or sha(p.read_bytes())!=r['sha256'] or p.stat().st_size!=r['bytes']:bad.append(n)
 extra=[str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in j['entries'] and p.name not in ('finalmanifest.json','manifest-verification.json')]
 dump('manifest-verification.json',dict(utc=utc(),status='PASS' if not bad and not extra else 'FAIL',entries=len(j['entries']),bad=bad,unexpected=extra,manifest_sha256=sha((L/'finalmanifest.json').read_bytes())))
 print('manifest verification',len(j['entries']),'entries','PASS' if not bad and not extra else 'FAIL');assert not bad and not extra
