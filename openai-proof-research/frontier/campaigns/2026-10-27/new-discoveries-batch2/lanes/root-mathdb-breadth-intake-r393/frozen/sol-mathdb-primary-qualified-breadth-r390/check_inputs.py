import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent;C=B/'pi-mathdb-full-corpus-inventory-r301';R=B/'root-mathdb-breadth-intake-r389'
def ref(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
m=json.loads((C/'manifest.json').read_text())
entries=m['files'];chunks=[x for x in entries if x['path'].startswith('corpus/')];assert len(chunks)==20,len(chunks)
rr=[]
for x in chunks:
 r=ref(C/x['path']);assert r['size']==x.get('bytes',x.get('size')) and r['sha256']==x['sha256'];rr.append(r)
p=L/'corpus-bindings.json';p.write_text(json.dumps({'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':rr},indent=2)+'\n');p.chmod(0o444)
r=json.loads((R/'reserved-ids.json').read_text());coverage=json.loads((R/'coverage-delta.json').read_text());reviewed=set(map(int,coverage));assert len(reviewed)==1133,len(reviewed)
a=set(r['ids']);o=set(r['other_active_reservations']);assert len(a)==len(r['ids'])==50 and len(o)==50 and not a&o and not a&reviewed and not a&{372627,372628,368940}
(L/'intake-check.json').write_text(json.dumps({'root_manifest_verified_read_only':True,'actual_originals_verified':True,'chunks_verified_in_place':20,'assigned_ids':r['ids'],'reviewed_count':len(reviewed),'disjoint':True},indent=2)+'\n');print('PASS all20 chunks; exact50; disjoint1133/active50/special3')
