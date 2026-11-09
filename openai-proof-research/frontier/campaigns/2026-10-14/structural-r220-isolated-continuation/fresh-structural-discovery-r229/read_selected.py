from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parent
name=sys.argv[1];f=R/name;b=f.read_bytes();ls=b.splitlines(keepends=True);off=[0]
for l in ls:off.append(off[-1]+len(l))
for spec in sys.argv[2:]:
 a,z=map(int,spec.split(':'));assert 1<=a<=z<=len(ls)
 part=b[off[a-1]:off[z]];assert part==b''.join(ls[a-1:z])
 rec={'local':name,'lines_inclusive':[a,z],'bytes_halfopen':[off[a-1],off[z]],'selected_sha256':hashlib.sha256(part).hexdigest(),'parser':'bytes.splitlines(keepends=True)','semantic_display':True}
 with (R/'reads.jsonl').open('a') as h:h.write(json.dumps(rec)+'\n')
 print('\nSELECTED',json.dumps(rec));print(part.decode('utf-8'))
