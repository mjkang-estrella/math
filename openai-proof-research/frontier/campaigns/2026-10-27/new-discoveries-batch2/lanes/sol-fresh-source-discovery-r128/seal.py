from research import *
excluded={'finalmanifest.json','manifest-verification.json'}
entries=[]
for p in sorted(H.rglob('*')):
 if p.is_file() and p.name not in excluded:
  b=p.read_bytes();entries.append({'path':str(p.relative_to(H)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
save('finalmanifest.json',{'schema':1,'scope':'lane only; self/detached verification excluded','entries':entries})
b=(H/'finalmanifest.json').read_bytes();m=json.loads(b)
for x in m['entries']:
 p=H/x['path'];assert p.stat().st_size==x['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256']
save('manifest-verification.json',{'status':'PASS','manifest_sha256':hashlib.sha256(b).hexdigest(),'payload_files':len(entries),'source_files':len(json.loads((H/'source-lock.json').read_text())),'counts_edited':False})
print(json.dumps(json.loads((H/'manifest-verification.json').read_text())))
