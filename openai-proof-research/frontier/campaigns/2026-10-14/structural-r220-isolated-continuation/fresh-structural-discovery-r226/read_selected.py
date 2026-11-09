from pathlib import Path
import sys,json,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r226')
P={'S':'Sharp-nodal-length-on-smooth-surfaces-September-23-2026','D':'Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026','P':'Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026'}
for arg in sys.argv[1:]:
 tag,name=arg.split(':',1); name,*sel=name.split('@'); rel='preprints/'+P[tag]+'/build/'+name
 b=(R/'private/upstream'/rel).read_bytes()
 if sel: start,end=map(int,sel[0].split(':'))
 else:start,end=0,len(b)
 offsets={0}; pos=0
 for line in b.splitlines(keepends=True):pos+=len(line);offsets.add(pos)
 assert start in offsets and end in offsets
 part=b[start:end]
 print('\nSEMANTIC EXACT',rel,'[%d,%d)'%(start,end),'SHA256',hashlib.sha256(part).hexdigest());print(part.decode())
 with (R/'READS.jsonl').open('a') as h:h.write(json.dumps({'path':rel,'start':start,'end':end,'sha256':hashlib.sha256(part).hexdigest(),'parser':'bytes.splitlines(keepends=True)','phase':'prefreeze; before extended deductions'})+'\n')
