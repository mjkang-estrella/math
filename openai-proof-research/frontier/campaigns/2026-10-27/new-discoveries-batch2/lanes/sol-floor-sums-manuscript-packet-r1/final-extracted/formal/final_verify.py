from pathlib import Path
import json,hashlib,re,sys
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def verify_audit(root):
 names=set();types=set();axioms=set();safety=set();origins=set();pending=None
 allowed={'propext','Classical.choice','Quot.sound'}
 for mod in json.loads((L/'audit-modules.json').read_text()):
  current=None
  receipt=json.loads((root/'logs'/(mod+'.guard.json')).read_text());assert receipt['exit_code']==0 and receipt['reason'] is None
  with (root/'logs'/(mod+'.log')).open() as f:
   for raw in f:
    s=raw.strip()
    if s.startswith('DECL|'):
     parts=s.split('|');n=parts[1];assert n not in names and parts[-1]=='false';names.add(n);origins.add(parts[3]);assert len(parts)==6;current=n
    if s.startswith('SAFETY|'):
     assert 'partial' not in s and 'unsafe' not in s.lower();safety.add(s.split('|')[1])
    if ' : ' in s:
     n=s.split(' : ',1)[0].removeprefix('@')
     if n in names:types.add(n)
    if current and (s==current or s.startswith(current+' ') or s.startswith(current+'.{') or s.startswith(current+' :')):types.add(current)
    if pending:
     pending[1]+=s
     if ']' not in s:continue
     n,values=pending;values=re.sub(r'\.\{[^}]*\}','',values);vals=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',values));assert vals<=allowed,(n,vals);axioms.add(n);pending=None
    elif s.startswith("'") and 'depends on axioms:' in s:
     n=s.split("'",2)[1];values=s.split('depends on axioms:',1)[1]
     if ']' in values:
      values=re.sub(r'\.\{[^}]*\}','',values);vals=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',values));assert vals<=allowed,(n,vals);axioms.add(n)
     else:pending=[n,values]
    elif s.startswith("'") and 'does not depend on any axioms' in s:axioms.add(s.split("'",2)[1])
 assert pending is None and names==types==axioms==safety,(len(names),len(types),len(axioms),len(safety),list(names-types)[:5])
 assert origins<=set(json.loads((L/'checked-modules.json').read_text()))
 return dict(declarations=len(names),origins=len(origins),allowed_axioms=sorted(allowed),names_sha256=hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest())
if '--original-audit' in sys.argv:
 a=verify_audit(L);(L/'original-audit-receipt.json').write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit()
if '--audit-only' in sys.argv:
 a=verify_audit(L);b=verify_audit(L/'fresh-replay');assert a==b
 (L/'audit-receipt.json').write_text(json.dumps(a,indent=2)+'\n');print(a);sys.exit()
manifest=json.loads((L/'final-manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']}
assert actual==set(manifest)
for n,h in manifest.items():assert sha(L/n)==h,n
for row in json.loads((L/'freeze.json').read_text()):assert sha(Path(row['original']))==sha(L/row['copy'])==row['sha256']
pins=json.loads((L/'pins.json').read_text());assert sha(Path(pins['lean']))==pins['lean_sha256']
for pin in pins['packages']:
 g=Path(pins['formal'])/'.lake/packages'/pin['name']/'.git';head=(g/'HEAD').read_text().strip()
 if head.startswith('ref: '):head=(g/head[5:]).read_text().strip()
 assert head==pin['revision']
assert sha(L/'frozen/primary/all-m-query.smt2')=='2864e469f3990f82b453b10649f93d9a177cafd2b9eb5869ae207ad5e3ebc704'
assert sha(L/'frozen/primary/z3-proof.sexpr')=='b102b526f33fe1cf0e1de3fd640ece58e8f4876a840215fae60a7edc5d2ce225'
for n in ['Reduction','Symmetry','Source','Expansion']:
 assert sha(L/(n+'.lean'))==sha(L/'frozen/sol-floor-sums-certificate-formal-r2'/(n+'.lean'))
a=verify_audit(L);b=verify_audit(L/'fresh-replay');assert a==b
for m in json.loads((L/'replay-modules.json').read_text()):
 p=m.replace('.','/')+'.lean';assert sha(L/p)==sha(L/'fresh-replay'/p)
 r=json.loads((L/'fresh-replay/logs'/(m+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None
for n,h in manifest.items():assert sha(L/n)==h
receipt=dict(integrity='PASS',audit=a,endpoint='PASS' if 'Endpoint' in json.loads((L/'checked-modules.json').read_text()) else 'HOLD',counts='9/39/next40; root alone accepts')
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
