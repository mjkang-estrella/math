from pathlib import Path
import hashlib,json,tarfile,io,gzip
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147')
def sha(b):return hashlib.sha256(b).hexdigest()
b=Path('sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(b);assert len(tree['tree'])==13223 and tree['truncated'] is False;mp={e['path']:e for e in tree['tree']}
source=json.loads((R/'SOURCE-AUTH.json').read_text())
for e in source['files']:
 b=(R/e['copy']).read_bytes();t=mp[e['canonical_path']];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size']==t['size'] and blob==e['git_blob_sha1']==t['sha'] and sha(b)==e['sha256']
primary=json.loads((R/'PRIMARY-AUTH.json').read_text());members=0
for e in primary:
 b=(R/e['incoming_path']).read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256']
 if not e['selected']:continue
 try:
  ar=tarfile.open(fileobj=io.BytesIO(b),mode='r:*')
  get=lambda name:ar.extractfile(name).read()
 except tarfile.ReadError:
  body=gzip.decompress(b) if b.startswith(b'\x1f\x8b') else b
  get=lambda name:body if name=='main.tex' else None
 for m in e['selected']:
  body=get(m['member']);copy=(R/m['copy']).read_bytes()
  assert body==copy and len(copy)==m['size'] and sha(copy)==m['sha256'];members+=1
originals=json.loads((R/'ORIGINALS-AUTH.json').read_text())['files'];stable=[];changed=[]
for e in originals:
 b=Path(e['original']).read_bytes();copy=(R/e['selected_copy']).read_bytes();assert len(copy)==e['selected_size'] and sha(copy)==e['selected_sha256']
 if len(b)==e['original_size'] and sha(b)==e['original_sha256']:
  stable.append(e['original'])
  if 'lines' in e:
   a,z=e['lines'];assert ''.join(b.decode().splitlines(keepends=True)[a-1:z]).encode()==copy
  else:assert b==copy
 else:changed.append(e['original'])
freeze=json.loads((R/'FREEZE.json').read_text());assert sha((R/'STATEMENT.md').read_bytes())==freeze['sha256'];assert sha((R/'CHECKPOINT.md').read_bytes())==freeze['prefreeze_checkpoint_sha256']
result={'tree_entries':13223,'source_bodies':len(source['files']),'primary_incoming':len(primary),'primary_selected_members':members,'stable_originals_since_late_capture':stable,'changed_originals_since_late_capture':changed,'frozen_statement_unchanged':True,'checkpoint_unchanged':True,'scope':'byte/membership checks only; no mathematical gate'}
(R/'AUTH-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='stable_originals_since_late_capture'}));print('stable originals',len(stable))
