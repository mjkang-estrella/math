import pathlib,json,hashlib,tarfile,importlib.util
L=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('delivery',L/'delivery.py');d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
manifest=json.loads((L/'final-manifest.json').read_text())
excluded={'final-manifest.json','final-verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(manifest),(actual-set(manifest),set(manifest)-actual)
for n,h in manifest.items():assert d.sha(L/n)==h,n
frozen=d.verify_inputs()
mods=json.loads((L/'replay-modules.json').read_text())
for mod in mods+['Audit']:
 n=mod.removeprefix('generated.')
 for base in [L,L/'fresh-replay']:
  r=json.loads((base/(n+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None,(base,n)
  assert r['command'][1:5]==['-j1','-M2700','-DwarningAsError=true','-DautoImplicit=false']
  if mod!='Audit':assert not (base/(n+'.log')).read_text()
 p=mod.replace('.','/')+'.lean';assert d.sha(L/p)==d.sha(L/'fresh-replay'/p)
audit=json.loads((L/'audit-receipt.json').read_text());fresh=json.loads((L/'fresh-replay/audit-receipt.json').read_text())
assert audit==fresh
assert audit['literal_endpoint']=='NOT_PROVED' and not audit['generated_partial_declarations']
with tarfile.open(L/'source-only.tar.gz') as t:
 for m in t.getmembers():
  assert not m.name.endswith(('.olean','.ilean','.o','.c')),m.name
  assert m.mtime==0 and m.uid==m.gid==0
  mutable={n.removeprefix('generated.')+s for n in mods+['Audit'] for s in ['.guard.json','.log','.console']}|{'audit-receipt.json'}
  if m.name not in mutable:
   h=hashlib.sha256()
   with t.extractfile(m) as f:
    while b:=f.read(1024*1024):h.update(b)
   assert h.hexdigest()==d.sha(L/'fresh-replay'/m.name),m.name
for n,h in manifest.items():assert d.sha(L/n)==h,n
receipt={'integrity':'PASS','strict_extracted_component_replay':'PASS','unconditional_literal_endpoint':'NOT_PROVED / HOLD','frozen_original_copy_pairs':frozen,'actual_declarations':audit['actual_declaration_count'],'modules_replayed':len(mods),'allowed_axioms':['propext','Classical.choice','Quot.sound'],'generated_partial_declarations':[],'novelty':'HOLD','acceptance':'HOLD','counts':'9 additional /39 total /next40; unchanged','manifest_sha256':d.sha(L/'final-manifest.json'),'archive_sha256':d.sha(L/'source-only.tar.gz'),'limitations':['Local rule proofs are not a closed certificate root or a SortedClampedBound proof.','Sampled RSS guards do not exclude unsampled transients.','Initial build orchestration briefly overlapped two Lean processes; final extracted replay is serial.']}
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
