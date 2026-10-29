import datetime,hashlib,json,zipfile
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent
S=P.parent/'sol-edge-irregulator-manuscript-packet-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
a=S/'edge-irregulator-manuscript-packet.zip'
assert sha(a)=='eec110ef7c3d49062da7dd211fca39227e2841ef9ec311921f463e197f4d6813'
assert sha(S/'packet/paper.pdf')=='6f46c49c1110b7a3fae8c750bf45b849fdc6dc0969b2916f2a1ce8965e398b90'
files={}
with zipfile.ZipFile(a) as z:
 names=z.namelist()
 assert not any(n.endswith(('.olean','.ilean','.o','.so','.ir')) for n in names)
 for n in names:
  if n.endswith('/'):continue
  p=S/'packet'/n
  assert p.is_file(),n
  h=hashlib.sha256()
  with z.open(n) as f:
   for c in iter(lambda:f.read(1048576),b''):h.update(c)
  assert sha(p)==h.hexdigest(),n
  files['packet/'+n]=h.hexdigest()
for n in ('edge-irregulator-manuscript-packet.zip','FINAL-RESULT.md','provenance.json'):
 files[n]=sha(S/n)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_lane':str(S),'files':files,'credit':0,'counts':[7,37],'root_scope':'Read full manuscript TeX and Result source. Independent final extracted replay launched separately; review full source/ordinary math/manuscript/formal/prior art required.','archive_entries':len(names)}
(P/'review-freeze.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'frozen_files':len(files),'archive_entries':len(names),'archive_sha256':sha(a)}))
