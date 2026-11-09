# Freeze/hash all inputs BEFORE reading any scientific statement content.
# Flat references only: originals are verified in place, nothing recursive is copied.
from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parents[1]; B=L.parent; CAMP=B.parent; REPO=B.parents[5]
def h(p):
    b=Path(p).read_bytes(); return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def entries(m): return m['files'] if isinstance(m,dict) else m
paths=[]; reports=[]
# 1. Root intake r359: full payload set equality + every manifest entry + every binding original/copy.
R=B/'root-mathdb-gram-intake-r359'; m=json.loads((R/'manifest.json').read_text()); E=entries(m)
actual={str(x.relative_to(R)) for x in R.rglob('*') if x.is_file()}-{'manifest.json','verification-receipt.json'}
assert actual=={e['path'] for e in E},'r359 payload set mismatch'
for e in E:
    r=h(R/e['path']); assert r['size']==e['size'] and r['sha256']==e['sha256'],e['path']; paths.append(R/e['path'])
paths+= [R/'manifest.json',R/'verification-receipt.json']
assert json.loads((R/'verification-receipt.json').read_text())['status']=='PASS'
nb=0
for e in json.loads((R/'bindings.json').read_text()):
    for q in (Path(e['original']),R/e['copy']):
        r=h(q); assert r['sha256']==e['sha256'] and r['size']==e['size'],q
    paths.append(Path(e['original'])); nb+=1
reports.append({'manifest':str(R/'manifest.json'),'checked_entries':len(E),'payload_set_equal':True,'bindings_checked':nb})
# 2. r355 active reservation (original, in place) + its manifest.
S=B/'root-mathdb-breadth-intake-r355'; mS=entries(json.loads((S/'manifest.json').read_text()))
for e in mS:
    r=h(S/e['path']); assert r['size']==e['size'] and r['sha256']==e['sha256'],e['path']; paths.append(S/e['path'])
paths.append(S/'manifest.json'); reports.append({'manifest':str(S/'manifest.json'),'checked_entries':len(mS)})
# 3. r301 corpus: twenty chunks verified IN PLACE against the immutable inventory manifest.
P=B/'pi-mathdb-full-corpus-inventory-r301'; mP=entries(json.loads((P/'manifest.json').read_text())); c=0
for e in mP:
    if not e['path'].startswith('corpus/'): continue
    r=h(P/e['path']); assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],e['path']; paths.append(P/e['path']); c+=1
assert c==20; paths.append(P/'manifest.json'); reports.append({'manifest':str(P/'manifest.json'),'checked_corpus_chunks':c})
# 4. r304 accepted-exclusion and historical registries.
X=B/'root-mathdb-accepted-exclusions-r304'; mX=entries(json.loads((X/'manifest.json').read_text()))
for e in mX:
    r=h(X/e['path']); assert r['sha256']==e['sha256'] and r['size']==e.get('size',r['size']),e['path']; paths.append(X/e['path'])
assert {'accepted-exclusions.json','historical-dispositions.json'}<={e['path'] for e in mX}
paths.append(X/'manifest.json'); reports.append({'manifest':str(X/'manifest.json'),'checked_entries':len(mX)})
# 5. Disjointness (IDs only; no statement content).
mine=json.loads((R/'reserved-ids.json').read_text()); ids=mine['ids']
queue=json.loads((R/'queue.json').read_text()); cov=json.loads((R/'coverage-delta.json').read_text())
other=json.loads((S/'reserved-ids.json').read_text())['ids']
assert mine['lane']==L.name and len(ids)==len(set(ids))==50 and [q['mathdb_id'] for q in queue]==ids
assert len(cov)==533 and not set(map(str,ids))&set(cov) and not set(ids)&set(other) and len(set(other))==50
assert 404067 not in ids and 364119 not in ids
disj={'reserved':50,'reviewed_533_overlap':0,'r355_active_overlap':0,'excluded_404067_364119_absent':True}
# 6. Governance / helper guard.
G=B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert h(G)['sha256']=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
paths+=[G,CAMP/'AGENTS.md',CAMP/'ledger.json',CAMP/'prior-campaign-context.json',REPO/'openai-proof-research/AGENTS.md' if (REPO/'openai-proof-research/AGENTS.md').exists() else CAMP.parents[3]/'AGENTS.md']
paths=[p for p in paths if Path(p).exists()]
rows=[h(p) for p in sorted(set(map(str,paths)))]
(L/'input-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified':reports,'disjointness':disj,'flat_original_refs':len(rows),'scientific_content_read_before_freeze':False,'corpus_copied':False},indent=2)+'\n')
print(json.dumps(reports));print(disj);print('BOUND',len(rows))
