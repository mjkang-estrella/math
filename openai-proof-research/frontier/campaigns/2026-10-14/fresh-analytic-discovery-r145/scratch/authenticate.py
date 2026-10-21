from pathlib import Path
import hashlib,json,tarfile,io,gzip
ROOT=Path.cwd();R=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145'
def sha(b):return hashlib.sha256(b).hexdigest()
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md','frontier/campaigns/2026-10-14/discovery-analytic-r144-parent/assessment.md']
base='frontier/campaigns/2026-10-14/'
paths += [base+'fresh-analytic-discovery-r144/'+s+'.md' for s in ['DERIVATION','LOCALIZATION-DETAILS','GAPS','READING-LIMITS','ISOLATION','CHRONOLOGY']]
paths += [base+d+'/'+f for d,fs in [('fresh-analytic-discovery-r10',['original-scope.md','candidate.md']),('coulomb-positive-r2',['original-scope.md','candidate.md']),('fresh-analytic-discovery-r54',['original-scope.txt','operation-comparison.md']),('fresh-analytic-discovery-r26',['original-scope.md'])] for f in fs]
paths += ['frontier/iterations/i217-quantitative-coulomb-monge.md','frontier/iterations/i220-quantitative-coulomb-continuation.md','frontier/experiments/i217_quantitative_coulomb_monge/analytic-attempt.md','frontier/experiments/i220_quantitative_coulomb_continuation/analytic-attempt.md']
originals=[{'path':p,'size':len((ROOT/p).read_bytes()),'sha256':sha((ROOT/p).read_bytes())} for p in paths]
(R/'ORIGINAL-AUTH.json').write_text(json.dumps({'note':'Named current original-byte identities recorded after reading, before final seal; not incoming detached packet authentication or original manifest membership. Originals not copied or executed.','files':originals},indent=2)+'\n')
b=(ROOT/'sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(b)['tree'];assert len(tree)==13223;tree={x['path']:x for x in tree}
for x in json.loads((R/'SOURCE-AUTH.json').read_text()):
 b=(R/x['selected_copy']).read_bytes();t=tree[x['path']];assert len(b)==x['size']==t['size'];assert sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==t['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'] in x['url']
raw_count=0;member_count=0;tar_matches=0
for x in json.loads((R/'PRIMARY-AUTH.json').read_text()):
 if 'incoming_sha256' in x:
  ident=x['id'].replace('-decoding-recovery','');p=R/'private/primary'/ident/'incoming.bin'
  if not p.exists():p=R/x['members'][0]['selected_path']
  b=p.read_bytes();assert len(b)==x['incoming_size'] and sha(b)==x['incoming_sha256'];raw_count+=1
  for m in x.get('members',[]):
   v=(R/m['selected_path']).read_bytes();assert len(v)==m['size'] and sha(v)==m['sha256'];member_count+=1
   if m.get('archive_member'):
    with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as t:assert t.extractfile(m['archive_member']).read()==v
    tar_matches+=1
  if ident=='1907.08425v1':
   v=gzip.decompress(b);assert v==(R/'private/primary/1907.08425v1/selected-original.tex').read_bytes();assert v.decode('latin1').encode('utf8')==(R/'private/primary/1907.08425v1/reading-latin1.txt').read_bytes()
  if ident=='1608.08780v1':assert gzip.decompress(b)==(R/x['members'][0]['selected_path']).read_bytes()
receipt={'complete_tree_entries':13223,'source_blobs_matched':11,'primary_incoming_matched':raw_count,'primary_selected_or_derivative_hashes_matched':member_count,'selected_tar_members_compared_to_incoming_in_memory':tar_matches,'single_tex_originals_and_latin1_derivative_matched':True,'named_originals_recorded':len(originals),'note':'Byte checks only. Does not imply complete semantic reading or independent publisher attestation. PDF text extraction is hashed, not independently replayed here.'}
(R/'AUTH-RECHECK.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
