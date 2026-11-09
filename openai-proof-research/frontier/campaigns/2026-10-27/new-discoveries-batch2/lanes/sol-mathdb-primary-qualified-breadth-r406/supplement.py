import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent.resolve();R=L.parents[5]
paths=[R/'sources/upstream.json',R/'sources/CONTENTS.md']
print(R)
a=[]
for p in paths:
 b=p.read_bytes();a.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'ancillary-references.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':a,'limitation':'Ancillary repository revision/catalogue read before this supplemental freeze due to initial path error; not used as scientific theorem or novelty evidence. Required intake/original/corpus/history anchors were frozen before scientific content.'},indent=2)+'\n')
