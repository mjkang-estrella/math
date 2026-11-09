from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent; L=R.parent
C=R/'frozen/sol-mathdb-circulant-15-source-prior-review-r382'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):assert p.is_file() and p.stat().st_size==s and sha(p)==h,str(p)
def files(p):return {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}
def put(n,x):(R/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert files(C)-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries:check(C/e['path'],e['sha256'],e['size'])
freeze=json.loads((C/'input-freeze.json').read_text());supp=json.loads((C/'supplemental-bindings.json').read_text())
for e in freeze['files']+supp['files']:check(Path(e['path']),e['sha256'],e['size'])
for x in freeze['exactsets']:
    root=Path(x['root']);assert files(root)==set(x['paths'])
    m=json.loads((root/'manifest.json').read_text())['files']
    assert files(root)-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
    for e in m:check(root/e['path'],e['sha256'],e['size'])
for name,key in [('root-mathdb-circulant-review-intake-r381/bindings.json','copy'),('root-mathdb-circulant-intake-r375/bindings.json','copy'),('sol-mathdb-circulant-15-certificate-review-r378/sourcebindings.json','payload')]:
    p=L/name
    for e in json.loads(p.read_text()):
        check(Path(e['original']),e['sha256'],e['size']);check(p.parent/e[key],e['sha256'],e['size'])
coverage=json.loads((R/'frozen/root-mathdb-breadth-intake-r383/coverage-delta.json').read_text())
held=json.loads((R/'frozen/root-mathdb-breadth-intake-r383/reserved-ids.json').read_text())['ids']
assert len(coverage)==1033 and len(set(held))==50 and not set(map(str,held))&set(coverage)
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines()]
seen=set(coverage)|set(map(str,held))|{'372627','372628','368940'};selected=[]
for x in queue:
    n=str(x['mathdb_id'])
    if n in seen or x['status']!='open' or x['statement_completeness']!='full':continue
    selected.append(x);seen.add(n)
    if len(selected)==50:break
assert len(selected)==50
reservation={'ids':[x['mathdb_id'] for x in selected],'lane':'sol-mathdb-primary-qualified-breadth-r386','status':'reserved_not_reviewed','other_active_reservations':held}
disposition={'mathdb_id':372628,'source_arxiv_v2':'PASS','published_source':'HOLD','math':'PASS inherited r378; no root replay','substantive':'conditional retention; no complete exclusion bridge','prior':'HOLD','formal_investment':'PARK','accepted_credit':0,'family_overlap':'372627; no separate credit presumption'}
def payload():return files(R)-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',reservation);put('disposition.json',disposition)
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    for n,x in [('coverage-delta.json',coverage),('queue.json',selected),('reserved-ids.json',reservation),('disposition.json',disposition)]:assert json.loads((R/n).read_text())==x
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'review_payloads':len(entries),'initial_originals':len(freeze['files']),'supplemental_originals':len(supp['files']),'upstream_exactsets':len(freeze['exactsets']),'reported_statement_reviews':len(coverage),'new_reservations':50,'other_reserved':50,'independent_math_replay':False,'credit':0})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(entries),'review payloads',len(coverage),'reviewed',len(selected),'new reserved')
