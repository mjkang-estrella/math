import pathlib,hashlib,shutil,zipfile,json
lane=pathlib.Path(__file__).parent
batch=lane.parent.parent
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for name,p in [('source-only.zip',lane.parent/'sol-four-attractor-source-formal-r1/source-only.zip'),('ledger.json',batch/'ledger.json'),('prior-campaign-context.json',batch/'prior-campaign-context.json'),('preliminary-review.md',lane.parent/'sol-four-attractor-preliminary-review-r1/review.md')]:
 before=h(p); q=lane/name;shutil.copyfile(p,q);after=h(p)
 assert before==h(q)==after
 records.append({'original':str(p),'copy':str(q),'sha256':before,'scientific':name=='source-only.zip'})
assert records[0]['sha256']=='651cb2a32c8be34fa3972599b7da470e9acfd7092634f1ac913595343db897de'
with zipfile.ZipFile(lane/'source-only.zip') as z:
 names=z.namelist();assert all(not pathlib.PurePosixPath(n).is_absolute() and '..' not in pathlib.PurePosixPath(n).parts for n in names)
 assert not any(n.endswith(('.olean','.ilean','.o','.so')) for n in names)
 z.extractall(lane/'extracted')
(lane/'freeze.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2)); print('\n'.join(names))
