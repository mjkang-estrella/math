from pathlib import Path
import json,hashlib,datetime
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');O=R/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118/packet'
h=lambda b:hashlib.sha256(b).hexdigest();b=(R/'sources/preprints-tree.json').read_bytes();assert h(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(b)['tree']};sr=[]
for row in json.loads((O/'source-identities.json').read_text()):
 b=(O/row['path']).read_bytes();e=tree[row['canonical_path']];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert e['size']==row['size']==len(b) and e['sha']==row['git_blob']==blob and h(b)==row['sha256'];sr.append(row['canonical_path'])
inc=json.loads((O/'incoming-identities.json').read_text());ir=[]
for row in inc['originals']:
 b=(R/row['original_path']).read_bytes();c=(O/row['copy_path']).read_bytes();assert len(c)==row['copy_size'] and h(c)==row['copy_sha256'];ir.append({'original_path':row['original_path'],'whole_original_matches_capture':h(b)==row['original_sha256'],'current_whole_sha256':h(b),'copy_matches':True})
pr=[]
for row in json.loads((O/'primary-identities.json').read_text()):
 if 'path' in row:
  assert h((O/row['path']).read_bytes())==row['sha256'];assert h((O/row['extract_path']).read_bytes())==row['extract_sha256'];pr.append(row['path'])
(O/'identity-recheck.json').write_text(json.dumps({'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'canonical_sources':len(sr),'incoming':ir,'downloaded_primary_and_extracts_matched':pr,'limits':'Current byte comparisons only. No new semantic reading, no first-read or future stability claim; web snapshots are manifest payloads, not downloaded PDF identities.'},indent=2)+'\n')
print('sources',len(sr),'selections',len(ir),'originals still equal',sum(x['whole_original_matches_capture'] for x in ir),'primary PDF/extract pairs',len(pr))
for x in ir:
 if not x['whole_original_matches_capture']:print('DRIFT',x['original_path'])
