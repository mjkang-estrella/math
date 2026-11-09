from pathlib import Path
import json,hashlib,zipfile,subprocess,sys
r=Path(__file__).resolve().parents[1]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
st=json.loads((r/'development-state.json').read_text());assert 'build:Nut8Final' in st['done'];assert 'build:PerSupport' in st['done']
fixes=json.loads((r/'source-fixes.json').read_text())
for x in fixes:x['passing_build_receipt']=st['done']['build:'+x['module']]['receipt']
(r/'source-fixes.json').write_text(json.dumps(fixes,indent=2)+'\n');fm={x['module']:x for x in fixes}
identity={};exceptions={}
for lane in ['r6q','r6p']:
 for p in (r/'inputs'/('nut-formal-'+lane)/'formal').glob('*.lean'):
  src=h(p);dest=h(r/'formal'/p.name);identity[str(p.relative_to(r/'inputs'))]={'input_sha256':src,'output_sha256':dest}
  if src!=dest:
   assert lane=='r6q' and p.stem in fm and src==fm[p.stem]['before_sha256'] and dest==fm[p.stem]['after_sha256']
   exceptions[p.stem]=fm[p.stem]
assert len(exceptions)==len(fixes)
(r/'inherited-identity.json').write_text(json.dumps({'status':'IDENTICAL_EXCEPT_AUTHORIZED_OBSERVED_COMPILATION_FIXES','module_copies':len(identity),'modified_unique_modules':len(exceptions),'sources':identity},indent=2)+'\n')
p=r/'REPRODUCE.md';s=p.read_text().replace('The original r6q and r6p Lean sources are retained byte-for-byte, including historical audit modules;', 'The inherited sources are retained byte-for-byte except the six observed compilation fixes documented in source-fixes.json; the r6p modules and fixed NutInterface are all byte-identical. Historical audit modules are retained;')
s+='\nThe initial packet replay in fresh-extracted stopped at FiniteSupport162. The six later compile fixes were checked in development mode. That initial replay is historical evidence, not final validation of the corrected packet. Resume the corrected, freshly extracted packet in fresh-final for final validation. Source-fixes.json records each failure, source hash change and passing strict build receipt.\n'
p.write_text(s)
p=r/'statement-correspondence.md';p.write_text(p.read_text()+'\nThe six permitted compilation fixes affect FiniteSupport162–166 (recursion limit only) and PerSupport (explicit empty-list membership simplification). The endpoint statement and all certificate branches are unchanged; see source-fixes.json.\n')
# Include compile-fix provenance in the portable packet.
p=r/'scripts/package.py';s=p.read_text().replace("'statement-correspondence.md']", "'statement-correspondence.md','source-fixes.json','inherited-identity.json']");p.write_text(s)
subprocess.run([sys.executable,'-I',str(p)],cwd=r,check=True)
st.setdefault('source_migrations',[]).append({'before':st['sources'],'after':h(r/'source-manifest.json'),'reason':'Freeze corrected packet and provenance; no additional Lean changes'})
st['sources']=h(r/'source-manifest.json');(r/'development-state.json').write_text(json.dumps(st,indent=2)+'\n')
f=r/'fresh-final';f.mkdir()
with zipfile.ZipFile(r/'nut-r7q-source.zip') as z:z.extractall(f)
assert not list(f.rglob('*.olean'))
print('Frozen corrected source-only packet and extracted into new empty fresh-final.')
