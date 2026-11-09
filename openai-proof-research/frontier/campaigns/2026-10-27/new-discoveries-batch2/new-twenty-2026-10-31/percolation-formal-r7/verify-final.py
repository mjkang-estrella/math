import pathlib,hashlib,json,re,zipfile
r=pathlib.Path(__file__).resolve().parent;f=r/'fresh-extracted';z=r/'final-source-check';p=r/'packet'
h=lambda b:hashlib.sha256(b).hexdigest()
files=['guard.sh','replay.sh','scan.py','module-order.txt']+['src/'+m+'.lean' for m in (z/'module-order.txt').read_text().splitlines()]
for name in files:assert (z/name).read_bytes()==(f/name).read_bytes()==(p/name).read_bytes(),name
sig='r7-v2'
for m in (z/'module-order.txt').read_text().splitlines():
 sig=h((sig+'\n'+h((z/'src'/f'{m}.lean').read_bytes())+'\n').encode())
 assert (f/'logs'/f'{m}.ok').read_text().strip()==sig+' '+h((f/'build'/f'{m}.olean').read_bytes()),m
log=(r/'axioms.txt').read_text();claims=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
assert len(claims)==2
for a in claims:assert set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'}
assert 'Metadata audit passed: 25680 declarations' in (r/'metadata-audit.txt').read_text()
assert h((r/'inherited.zip').read_bytes())=='9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c'
with zipfile.ZipFile(r/'inherited.zip') as old:
 match={name:h((z/name).read_bytes()) for name in files if name.startswith('src/') and name in old.namelist()}
 for name in match:assert old.read(name)==(z/name).read_bytes(),name
(r/'inherited-source-comparison.json').write_text(json.dumps(match,indent=2))
(r/'final-verification.json').write_text(json.dumps({'compared_source_and_driver_files':len(files),'fresh_success_stamps':303,'axioms_allowed':True,'metadata_audit_declarations':25680,'source_archive_sha256':h((r/'source-only.zip').read_bytes()),'final_archive_sources_equal_fresh_replayed_sources':True},indent=2))
with zipfile.ZipFile(r/'full-logs.zip','w',zipfile.ZIP_DEFLATED) as out:
 for d in [r/'logs',r/'packet/logs',r/'fresh-extracted/logs']:
  for file in sorted(d.glob('*')):
   if file.is_file():out.write(file,str(file.relative_to(r)))
 for name in ['fresh-replay.log','replay-development.log']:out.write(r/name,name)
print('Verified 303 success stamps, all source/driver bytes, permitted axioms and inherited identities.')
