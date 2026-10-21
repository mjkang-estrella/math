from pathlib import Path
import hashlib,json,tarfile,io
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146')
def sha(b):return hashlib.sha256(b).hexdigest()
b=Path('sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(b);assert len(tree['tree'])==13223 and tree['truncated'] is False
t={e['path']:e for e in tree['tree']}
s=json.loads((r/'SOURCE-AUTH.json').read_text())
for e in s['entries']:
 b=(r/e['selected_path']).read_bytes();t0=t[e['canonical_path']]
 assert len(b)==e['size']==t0['size'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['gitblob_sha1']==t0['sha']
 assert e['url']=='https://raw.githubusercontent.com/openai/math/'+s['pin']+'/'+e['canonical_path']
p=json.loads((r/'PRIMARY-AUTH.json').read_text()); members=0
for e in p:
 dest=r/'private/primary'/e['id'];b=(dest/'incoming.bin').read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256']
 with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as archive:
  for m in e['selected']:
   incoming=archive.extractfile(m['member']).read();selected=(dest/'selected'/m['member']).read_bytes()
   assert incoming==selected and len(selected)==m['size'] and sha(selected)==m['sha256'];members+=1
  actual={str(f.relative_to(dest/'selected')) for f in (dest/'selected').rglob('*') if f.is_file()}
  assert actual=={m['member'] for m in e['selected']}
o=json.loads((r/'ORIGINALS-AUTH.json').read_text())
for e in o['entries']:
 b=Path(e['original_path']).read_bytes();assert b==(r/e['selected_path']).read_bytes()
 assert len(b)==e['size'] and sha(b)==e['sha256']
res=dict(tree_entries=13223,canonical_source_bodies=len(s['entries']),incoming_primary_archives=len(p),selected_members=members,late_original_identities=len(o['entries']),all_matched=True,limits='Byte identity and selected membership only; no original seal, semantic completeness, or mathematical gate.')
(r/'AUTH-CHECK.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
