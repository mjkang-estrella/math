from pathlib import Path
import sys,json,hashlib,datetime
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r225')
f=sys.argv[1];b=(R/f).read_bytes();a=int(sys.argv[2]);z=int(sys.argv[3]);lines=b.splitlines(keepends=True);ends=[0]
for l in lines:ends.append(ends[-1]+len(l))
assert 1<=a<=z<=len(lines)
s=b[ends[a-1]:ends[z]]
print(f'READ {f} lines {a}-{z} bytes [{ends[a-1]},{ends[z]}) SHA256 {hashlib.sha256(s).hexdigest()}')
for n,l in enumerate(lines[a-1:z],a):print(f'{n}: '+l.decode('utf8').rstrip('\r\n'))
with (R/'semantic-reads.jsonl').open('a') as out:out.write(json.dumps({'file':f,'line_start':a,'line_end':z,'byte_start':ends[a-1],'byte_end':ends[z],'sha256':hashlib.sha256(s).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parser':'bytes.splitlines(keepends=True)'})+'\n')
