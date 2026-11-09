from pathlib import Path
import json,hashlib,tarfile,datetime,re
R=Path(__file__).resolve().parent
def check(p,e):
 assert p.is_file() and p.stat().st_size==e['size'] and hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'],str(p)
f=json.loads((R/'manifest.json').read_text())['files']
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
assert actual==set(f)
for n,e in f.items():check(R/n,e)
refs=json.loads((R/'freeze.json').read_text())['bindings']
for e in refs:check(Path(e['path']),e)
assert not list(R.rglob('*.olean'))
D=R/'replay';s=json.loads((D/'source-manifest.json').read_text())
for n,h in s.items():assert hashlib.sha256((D/n).read_bytes()).hexdigest()==h
with tarfile.open(R/'source-only.tar.gz') as t:
 assert len(t.getnames())==9 and set(t.getnames())==set(s)|{'source-manifest.json'}
 for m in t:assert m.isfile() and m.mtime==0 and t.extractfile(m).read()==(D/m.name).read_bytes()
r=json.loads((D/'replay-receipt.json').read_text())
assert r['component_status']=='PASS' and r['actual_declaration_count']==87 and r['endpoint']=='Cayley.literal_source_claim_false'
assert json.loads((D/'pins-before.json').read_text())==json.loads((D/'pins-after.json').read_text())
a=(D/'Audit.log').read_text();i=(D/'Inventory.log').read_text()
names=re.findall(r'^INVENTORY\|([^|]+)\|(Definitions|Witness)\|false$',i,re.M)
bs=[b for b in re.split(r'(?=^DECL\|)',a,flags=re.M) if b.startswith('DECL|')]
ns=[re.match(r'DECL\|([^|]+)\|',b)[1] for b in bs]
assert len(ns)==len(set(ns))==len(names)==87 and set(ns)=={n for n,_ in names}
for n,b in zip(ns,bs):assert re.search(r'^'+re.escape(n)+r'(?:\s|\.)',b,re.M)
assert '⋯' not in a+i
assert len(re.findall(r'^TYPE\|',i,re.M))==87
for x in r['declarations']:
 assert not x['unsafe'] and not x['safety'].endswith('.partial') and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}
for m in ['Definitions','Witness','Audit','Inventory']:
 g=json.loads((D/(m+'.guard.json')).read_text());assert g['exit_code']==0 and g['reason'] is None
(R/'verification-receipt.json').write_text(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payloads':len(f),'original_bindings':len(refs),'manifest_sha256':hashlib.sha256((R/'manifest.json').read_bytes()).hexdigest(),'fresh_review_replay':True,'declarations':87,'source':'PASS_explicit_notation_interpretation','math':'PASS','formal':'PASS_with_supplemental_audit','substantive':'FAIL_source_p280_already_implies_literal_negation','novelty':'HOLD','acceptance':'ROOT_SEPARATE','counts':'9 additional / 39 total / next 40'},indent=2)+'\n')
print('PASS',len(f),'payloads',len(refs),'original references; fresh replay; substantive FAIL')
