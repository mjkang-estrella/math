from research import *
TREE=json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']
records=[]
for e in TREE:
 if 'Elementary-Positivity-of-Chromatic' not in e['path'] or e['type']!='blob' or not e['path'].endswith(('.tex','.bib','.md')):continue
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read();gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==e['size'] and gh==e['sha']
 p=PRIVATE/'upstream'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 records.append(dict(path=e['path'],url=url,size=len(b),git_blob=gh,sha256=sha(b),acquired_utc=now(),read_status='acquired; later read log governs'))
save('source-acquisition.json',records);print(len(records),'authenticated pinned blobs acquired')
