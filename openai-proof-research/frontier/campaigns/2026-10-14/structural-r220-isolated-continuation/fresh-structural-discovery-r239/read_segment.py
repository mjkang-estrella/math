import sys,json,hashlib,datetime
from pathlib import Path
R=Path(__file__).parent
items=json.loads((R/'private/primary-boundaries.json').read_text())
e=next(e for e in items if e['alias']==sys.argv[1]); b=(R/'private/canonical'/e['path']).read_bytes(); ls=b.splitlines(keepends=True)
a=int(sys.argv[2]);z=int(sys.argv[3]);assert 1<=a<=z<=len(ls)
lo=sum(map(len,ls[:a-1])); hi=sum(map(len,ls[:z])); selected=b[lo:hi]
assert selected==b''.join(ls[a-1:z])
masked=[]
for x,y,label in e['candidate_masks']:
 if lo<=x<hi:
  selected=selected.replace(b[x:y],b'[MASKED editorial/driver metadata]\n',1);masked.append([x,y,label])
print(f"{e['alias']} byte-lines {a}..{z}; bytes [{lo},{hi}); masks {masked}")
print(selected.decode(),end='')
with (R/'private/read-events.jsonl').open('a') as f:f.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'alias':e['alias'],'line_start':a,'line_end_inclusive':z,'byte_start':lo,'byte_end_exclusive':hi,'masked':masked,'display_sha256':hashlib.sha256(selected).hexdigest(),'event':'semantic display; coverage subject to tool-output completion'})+'\n')
