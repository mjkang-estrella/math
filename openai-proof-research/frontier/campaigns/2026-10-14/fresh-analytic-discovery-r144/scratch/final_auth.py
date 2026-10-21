from pathlib import Path
import hashlib,json,tarfile,io
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144')
sha=lambda b:hashlib.sha256(b).hexdigest()
b=Path('sources/preprints-tree.json').read_bytes()
assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(b); assert len(tree['tree'])==13223
entries={e['path']:e for e in tree['tree']}
src=json.loads((r/'SOURCE-AUTH.json').read_text())
for e in src['files']:
    b=(r/e['local']).read_bytes(); t=entries[e['canonical_path']]
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==e['size']==t['size']
    assert blob==e['git_blob_sha1']==t['sha'] and sha(b)==e['sha256']
prim=json.loads((r/'PRIMARY-AUTH.json').read_text());raws=members=0
for e in prim:
    if 'failure' in e: continue
    p=r/'private/primary'/e['id'];b=(p/'incoming.bin').read_bytes()
    assert len(b)==e['incoming_size'] and sha(b)==e['incoming_sha256'];raws+=1
    with tarfile.open(fileobj=io.BytesIO(b)) as archive:
        for m in e['selected_members']:
            data=archive.extractfile(m['name']).read()
            selected=(p/'selected'/m['name']).read_bytes()
            assert data==selected and len(data)==m['size'] and sha(data)==m['sha256']
            members+=1
    actual={x.relative_to(p/'selected').as_posix() for x in (p/'selected').rglob('*') if x.is_file()}
    assert actual=={x['name'] for x in e['selected_members']}
originals=json.loads((r/'LOCAL-ORIGINAL-AUTH.json').read_text())
for e in originals:
    b=Path(e['path']).read_bytes()
    assert len(b)==e['size'] and sha(b)==e['sha256'],e['path']
out={'tree_entries':13223,'source_blobs_matched':len(src['files']),
 'primary_incoming_archives_matched':raws,'primary_selected_members_matched':members,
 'local_original_records_matched':len(originals),
 'limits':'No fresh remote identity or mathematical verification. Originals matched the earlier local-auth record; no inherited membership manifest used.'}
(r/'AUTH-RECHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
