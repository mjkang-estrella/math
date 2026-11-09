from research import *
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree'];r=[]
for e in tree:
 if any(forbidden(c) for c in pathlib.PurePosixPath(e['path']).parts):continue
 if 'An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/' not in e['path'] or e['type']!='blob' or not e['path'].endswith(('.tex','.bib','.md')):continue
 u='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path'];b=urllib.request.urlopen(u,timeout=40).read();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==e['size'] and g==e['sha']
 p=PRIVATE/'upstream'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);r.append(dict(path=e['path'],url=u,size=len(b),git_blob=g,sha256=sha(b),acquired_utc=now()))
save('companion-acquisition.json',r);print(len(r),'companion blobs authenticated')
