from research import *
records=[]
for name in ['context-bindings.json','history-bindings.json']:
 for r in json.loads((PRIVATE/name).read_text()):
  assert not any(forbidden(c) for c in pathlib.PurePosixPath(r['path']).parts)
  b=(ROOT/r['path']).read_bytes()
  records.append(dict(path=r['path'],baseline_observed_utc=r['observed_utc'],baseline_sha256=r['sha256'],current_observed_utc=now(),current_sha256=sha(b),same_bytes=sha(b)==r['sha256'],scope='named current baseline only'))
save('originals-preservation.json',dict(recorded_utc=now(),records=records,all_named_bytes_unchanged=all(r['same_bytes'] for r in records),historical_whole_parent_claim=False,whole_project_claim=False))
mutable='frontier/NEW-TEN-2026-10-14.md'
assert all(r['same_bytes'] for r in records if r['path']!=mutable)
save('preservation-scope.json',dict(recorded_utc=now(),immutable_named_count=17,immutable_named_bytes_unchanged=True,mutable_ledger_path=mutable,mutable_ledger_changed=any(not r['same_bytes'] for r in records if r['path']==mutable),mutable_ledger_role='observation only, not a mathematical binding; no write by this lane; writer not identified',baseline_copies_unchanged=all(sha((OUT/r['copy']).read_bytes())==r['sha256'] for name in ['context-bindings.json','history-bindings.json'] for r in json.loads((PRIVATE/name).read_text()))))
# Authentication replay is separate from semantic reads.
tree=json.loads((PRIVATE/'context/sources/preprints-tree.json').read_text());idx={x['path']:x for x in tree['tree']};auth=[]
for name in ['source-acquisition.json','polymatroid-acquisition.json','companion-acquisition.json']:
 for r in json.loads((PRIVATE/name).read_text()):
  b=(PRIVATE/'upstream'/r['path']).read_bytes();t=idx[r['path']];gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert t['size']==len(b)==r['size'] and t['sha']==gh==r['git_blob'] and sha(b)==r['sha256']
  auth.append(r)
save('source-authentication-replay.json',dict(observed_utc=now(),pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',tree_entries=len(tree['tree']),tree_truncated=tree['truncated'],tree_sha256=sha((PRIVATE/'context/sources/preprints-tree.json').read_bytes()),authenticated_blobs=len(auth),semantic_read_authority='read-ledger.json only'))
public={'recorded_utc':now(),'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','rights':'metadata only; originals private under original rights','pinned_sources':auth,'external':[]}
for name in ['primary-acquisition.json','bh-acquisition.json','union-acquisition.json']:
 j=json.loads((PRIVATE/name).read_text());public['external']+=j if isinstance(j,list) else [j]
(OUT/'packet/public/provenance.json').write_text(json.dumps(public,indent=2)+'\n')
print('17 named immutable originals unchanged; mutable campaign-ledger change separately recorded;',len(auth),'pinned source blobs reauthenticated')
