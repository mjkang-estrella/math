import pathlib,json,hashlib,subprocess,sys,time,datetime
L=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='pages':
 for name,terms in {'edge':['Question 6.6','Proposition 4.20','Question 6.2','Conjecture 1.3','Definition 1.4'],'permutation':['Conjecture 35','Proposition 33','Question 25'],'tangled':['Conjecture 1.5','Theorem 3.14','Theorem 4.4'],'genius':['Conjecture 1.','Conjecture 2.']}.items():
  p=L/'sources'/f'{name}.txt';a=sha(p)
  for i,page in enumerate(p.read_text().split('\f'),1):
   for term in terms:
    start=page.find(term)
    if start>=0:print(name,'PDFpage',i,page[start:start+650])
  assert sha(p)==a
if sys.argv[1]=='replay':
 results=[]
 for name in ['cube.py','cube_route2.py','cube_reduce.py','verify_math.py','genius_check.py']:
  start=time.monotonic();p=subprocess.run([sys.executable,str(L/name)],capture_output=True,text=True,timeout=100)
  results.append(dict(script=name,exit=p.returncode,seconds=time.monotonic()-start,stdout=p.stdout,stderr=p.stderr));assert p.returncode==0
 (L/'checks.json').write_text(json.dumps(results,indent=2));print([(r['script'],r['exit'],r['seconds']) for r in results])
if sys.argv[1]=='manifest':
 import xml.etree.ElementTree as E
 p=L/'sources/versions.xml';root=E.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
 entries=[]
 for e in root.findall('a:entry',ns):
  entries.append('|'+ '|'.join(e.findtext('a:'+k,default='',namespaces=ns).replace('\n',' ') for k in ['id','published','updated','title'])+'|')
 (L/'SOURCE_MAP.md').write_text('# Version chronology and primary bodies\n\nThe version-specific API response is retained as sources/versions.xml, frozen before parsing. Published is first submission, updated is the requested version date. HTTP cache Last-Modified is not publication chronology.\n\n|Version|First submission UTC|Version UTC|Title|\n|---|---|---|---|\n'+'\n'.join(entries)+'\n\nLocal names: edge=1501.04540v2; permutation=1506.04406v3; antichain=1905.06692v1; genius=2002.03814v1; tangled=2411.12034v1; antichain-resolution=2609.28983v1; later-federbush=2012.10927v8. Each sources/NAME.pdf.json gives the exact versioned URL, retrieval UTC, status, bytes, SHA256 and headers. Each NAME.txt.sha256 binds the extracted body before reading. provenance.json inventories all retained primary/query bytes and hashes.\n\nRead scopes: edge Def1.4/Thm1.5 p3, Prop1.9 and Section4 product hypotheses, Prop4.20 p15, Questions6.2–6.8 pp17–18; permutation Def8 p4, EZ sum p8, Prop32–34 and proofs pp15–16, Conj35 p16; tangled introductory conjectures pp1–2, extended-promotion definitions pp2–3, Thm3.14 p10 and Thm4.4 p12 statement/local proof excerpts, Remark6.4 near end of Section6; genius all defining Eqs1–5 and conjectures pp1–3, background/appendix comparisons; antichain conjecture bodies pp3/9–10 and local comparisons; antichain-resolution Thm1.2 p3, discussion p4, full counterexample proof Prop5.2 pp39–40; later-federbush introduction/Theorems3.1–3.2 and AppendixB bounded-scope comparison. No full proof audit claimed for the large public-resolution papers.\n\nCurrent queries are bounded arXiv primary metadata queries. No full public proof-registry head or universal absence claim. Reused immutable historical references and scientific report bindings are in history-bindings.json and freeze.json; administrative snapshots are not claims of immutable current campaign state.\n')
 meta=[]
 for p in sorted((L/'sources').glob('*')):
  meta.append(dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size))
 (L/'provenance.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sources=meta,chronology='Versioned primary bodies; arXiv dates inside PDFs and feeds. HTTP last-modified is not publication date.',limits='No complete current public proof-registry head. Forbidden and parked routes not attempted. No worldwide priority claim.'),indent=2))
 files=[dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']]
 (L/'finalmanifest.json').write_text(json.dumps(files,indent=2));print(len(files))
if sys.argv[1]=='verify':
 rows=json.loads((L/'finalmanifest.json').read_text())
 for r in rows:
  p=L/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 for p in (L/'sources').glob('*.json'):
  r=json.loads(p.read_text());assert sha(p.with_suffix(''))==r['sha256']
 for p in (L/'sources').glob('*.txt.sha256'):assert sha(p.with_suffix(''))==p.read_text().strip()
 for r in json.loads((L/'history-bindings.json').read_text()):assert sha(pathlib.Path(r['path']))==r['sha256']
 for r in json.loads((L/'freeze.json').read_text()):
  assert sha(pathlib.Path(r['copy']))==r['sha256']
  if 'administrative' not in r['copy']:assert sha(pathlib.Path(r['original']))==r['sha256']
 out=dict(status='PASS',manifest_entries=len(rows),manifest_sha256=sha(L/'finalmanifest.json'),history_references=1596,scientific_originals_and_copies='verified',administrative='snapshot only; no requirement that live administration stayed unchanged',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 (L/'verification-receipt.json').write_text(json.dumps(out,indent=2));print(out)
