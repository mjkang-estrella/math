from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
coverage={
'target-vor':[(345,435),(1110,1245)],'target-correction':[(1,220)],
'aldous-book':[(3570,3665),(4850,4880)],'dense-cover':[(240,300),(918,1065)],'mixing-cover':[(25,65),(250,290)],
'2610.40645v1':[(175,205),(269,293),(1710,1724)],
'2610.40598v1':[(190,220),(618,651)],'2610.40555v1':[(240,266),(850,885),(918,942)],
'2610.40472v1':[(309,365),(391,425)],'2610.39967v1':[(38,58),(314,368),(955,979)],
'2610.38893v1':[(1028,1085),(1997,2020)],'2610.38877v1':[(45,85),(625,665)],
'2610.38510v1':[(125,185),(1675,1694)],'2610.37618v1':[(146,162),(280,300),(980,1005)],
'2610.37521v1':[(270,310),(480,500),(1570,1598)]}
rows=[]
for n,ranges in coverage.items():
 p=L/'texts'/(n+'.txt');lines=p.read_text().split('\n')
 rows.append(dict(text=str(p),sha256=H(p),scope='bounded statement/proof neighborhoods; not a full independent audit',passages=[dict(first_line=a,last_line=b,pdf_page=1+'\n'.join(lines[:a-1]).count('\f'),text='\n'.join(lines[a-1:b])) for a,b in ranges]))
(L/'body-coverage.json').write_text(json.dumps(rows,indent=2)+'\n')
admin=[]
for p in sorted((L/'admin').rglob('*.json')):
 d=json.loads(p.read_text());admin.append(dict(path=str(p),sha256=H(p),keys=list(d),accepted_entries=len(d.get('accepted',[]))))
(L/'provenance.json').write_text(json.dumps(dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),solo=True,assigned_lane=str(L),counts=[9,39,40],administrative_snapshots=admin,guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',limits=dict(address_space=536870912,group_rss=536870912,cpu_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),retrieval='access.py, no retries; no browsers or denied routes',source_freeze='Original bytes and frozen-live copy SHA256 verified before extraction; old scientific inputs bound/copied before reading; administrative snapshots only; history report bytes hashed before decoding, immutable references only',new_result='Unreviewed elementary renewal bridge; no accepted outcome',excluded_from_manifest=['finalmanifest.json','verification-receipt.json']),indent=2)+'\n')
files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=H(p)) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']]
(L/'finalmanifest.json').write_text(json.dumps(dict(files=files),indent=2)+'\n')
print(json.dumps(dict(manifest_files=len(files),body_families=10,counts=[9,39,40])))
