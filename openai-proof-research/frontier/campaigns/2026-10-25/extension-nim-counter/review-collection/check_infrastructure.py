from pathlib import Path
import importlib.util,json,copy,io,zipfile,hashlib,stat,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-25/thirty-proof-campaign')
WORK=ROOT.parent/'extension-nim-counter/review-collection'
spec=importlib.util.spec_from_file_location('collector_review', ROOT/'collect_release.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
current=json.loads((ROOT/'ledger.json').read_text());old=json.loads((ROOT.parent/'twenty-proof-campaign/ledger.json').read_text())
report={'snapshot_count':current['verified_count'],'ledger_checks':{},'old_preserved':{},'accepted_archives':[],'zip_checks':{}}
for name,x in [('old20',old),('current28',current)]:
 try:c.validate_ledger(x);report['ledger_checks'][name]='UNEXPECTED PASS'
 except SystemExit as e:report['ledger_checks'][name]='REJECT: '+str(e)
synthetic=copy.deepcopy(current)
while len(synthetic['verified'])<30:
 e=copy.deepcopy(synthetic['verified'][-1]);e['ordinal']=len(synthetic['verified'])+1;e['mathdb_id']=900000+e['ordinal'];e['package']='outcomes/test-'+str(e['ordinal']);e['archive']='output/release/thirty-proofs/test-'+str(e['ordinal'])+'.zip';synthetic['verified'].append(e)
synthetic['verified_count']=30
for name,x in [('advertised30_length28',copy.deepcopy(current)),('advertised28_length30',copy.deepcopy(synthetic))]:
 x['verified_count']=30 if name=='advertised30_length28' else 28
 try:c.validate_ledger(x);report['ledger_checks'][name]='UNEXPECTED PASS'
 except SystemExit as e:report['ledger_checks'][name]='REJECT: '+str(e)

for name,mutate in [('duplicate_id',lambda x:x['verified'][-1].update(mathdb_id=x['verified'][0]['mathdb_id'])),('bad_replay',lambda x:x['verified'][-1].update(replay='FAIL')),('bad_package_path',lambda x:x['verified'][-1].update(package='outcomes/../../outside')),('bad_archive_path',lambda x:x['verified'][-1].update(archive='output/release/../../outside.zip')),('bad_ordinal',lambda x:x['verified'][-1].update(ordinal=29))]:
 x=copy.deepcopy(synthetic);mutate(x)
 try:c.validate_ledger(x);report['ledger_checks'][name]='UNEXPECTED PASS'
 except SystemExit as e:report['ledger_checks'][name]='REJECT: '+str(e)
for a,b in zip(old['verified'],current['verified'][:20]):
 report['old_preserved'][str(a['mathdb_id'])]={'id_same':a['mathdb_id']==b['mathdb_id'],'hash_same':a['archive_sha256']==b['archive_sha256']}
replays=c.replay_records()
for e in current['verified']:
 path=c.PROJECT/e['archive'];raw=path.read_bytes()
 assert hashlib.sha256(raw).hexdigest()==e['archive_sha256']
 with zipfile.ZipFile(path) as z:
  prefix=c.validate_members(z);h=c.validate_acceptance(z,prefix,e,replays)
  canonical=(ROOT/e['package']).resolve()
  row={'id':e['mathdb_id'],'archive_sha256':e['archive_sha256'],'proof_sha256':h,'manifest':'PASS','canonical_acceptance':'PASS'}
  if e['mathdb_id']!=336488:
   row['review_canonical_bytes_same']=z.read(prefix+'review.md')==(canonical/'review.md').read_bytes()
   row['verifier_matches_current_root']=z.read(prefix+'verify_outcome.py')==(ROOT/'verify_outcome.py').read_bytes()
   row['pins_matches_current_root']=z.read(prefix+'pins.json')==(ROOT/'pins.json').read_bytes()
  report['accepted_archives'].append(row)
def zipcheck(name,members):
 b=io.BytesIO()
 sums=''.join(hashlib.sha256(data).hexdigest()+'  '+n.removeprefix('root/')+'\n' for n,data,mode in members)
 with zipfile.ZipFile(b,'w') as z:
  for n,data,mode in members:
   zi=zipfile.ZipInfo(n);zi.external_attr=mode<<16;z.writestr(zi,data)
  z.writestr('root/SHA256SUMS',sums)
 b.seek(0)
 try:
  with zipfile.ZipFile(b) as z:c.validate_members(z)
  report['zip_checks'][name]='ACCEPT'
 except SystemExit as e:report['zip_checks'][name]='REJECT: '+str(e)
zipcheck('ordinary',[('root/a.txt',b'a',0o100644)])
zipcheck('parent_traversal',[('root/../a.txt',b'a',0o100644)])
zipcheck('backslash',[('root/a\\b.txt',b'a',0o100644)])
zipcheck('symlink',[('root/a.txt',b'target',0o120777)])
zipcheck('dot_alias',[('root/a.txt',b'a',0o100644),('root/./a.txt',b'b',0o100644)])
zipcheck('double_slash_alias',[('root/a.txt',b'a',0o100644),('root//a.txt',b'b',0o100644)])
(WORK/'checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
