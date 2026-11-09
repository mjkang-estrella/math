import json,hashlib,os,sys
R=sys.argv[1]
def h(p):
    s=hashlib.sha256();n=0
    with open(p,'rb') as f:
        for c in iter(lambda:f.read(1<<20),b''): s.update(c);n+=len(c)
    return s.hexdigest(),n
m=json.load(open(os.path.join(R,'manifest.json')))
res={'counts':m['counts'],'excluded':m['excluded_from_manifest'],'files':0,'file_bad':[],'chunks':[],'frozen_inputs':[],'fi_bad':[]}
for f in m['files']:
    p=os.path.join(R,f['path'])
    ok=os.path.isfile(p) and h(p)==(f['sha256'],f['bytes'])
    res['files']+=1
    if not ok: res['file_bad'].append(f['path'])
    if f['path'].startswith('corpus/'): res['chunks'].append([f['path'],f['bytes'],f['sha256'],ok])
for f in m['frozen_inputs']:
    p=f['path'] if os.path.isabs(f['path']) else os.path.join(R,f['path'])
    ok=os.path.isfile(p) and h(p)==(f['sha256'],f['bytes'])
    res['frozen_inputs'].append([f['path'],f['bytes'],f['sha256'],ok])
print(json.dumps(res,indent=1))
