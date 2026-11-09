from pathlib import Path
import sys,json,hashlib,datetime
ROOT=Path(__file__).parent
for spec in sys.argv[1:]:
 name,span=spec.rsplit(':',1); lo,hi=map(int,span.split('-'))
 p=ROOT/'private/source355/build'/name
 data=p.read_bytes(); lines=data.splitlines(keepends=True)
 assert 1<=lo<=hi<=len(lines)
 a=sum(map(len,lines[:lo-1])); b=sum(map(len,lines[:hi])); body=data[a:b]
 assert body==b''.join(lines[lo-1:hi])
 entry={'file':str(p.relative_to(ROOT)),'line_start':lo,'line_end_inclusive':hi,'byte_start':a,'byte_end_exclusive':b,'sha256':hashlib.sha256(body).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'exact raw UTF8 mathematical passage; byte splitlines parser','coverage':'display requested; any tool truncation must be recovered separately'}
 with (ROOT/'private/semantic-reads.jsonl').open('a') as f: f.write(json.dumps(entry)+'\n')
 print('\nPASSAGE '+json.dumps(entry)+'\n'+body.decode())
