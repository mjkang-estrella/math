from pathlib import Path
import sys,json,hashlib,datetime
R=Path(__file__).resolve().parent
roots={'A':'A-Codimension-One-Bound-for-the-Singular-Set-of-a-Stationary-Integral-Varifold-October-5-2026','B':'Almost-everywhere-regularity-of-stationary-integral-varifolds-September-23-2026'}
for arg in sys.argv[1:]:
 key,rel,lo,hi=arg.split(':');p=R/'private/upstream/preprints'/roots[key]/'build'/rel
 b=p.read_bytes(); ls=b.splitlines(keepends=True);a=int(lo)-1;z=len(ls) if hi=='end' else int(hi)
 assert 0<=a<z<=len(ls)
 start=sum(map(len,ls[:a]));stop=start+sum(map(len,ls[a:z]));part=b[start:stop]
 print('\nEXACT '+key+'/'+rel+f' lines {a+1}..{z}; bytes [{start},{stop})/{len(b)} SHA256 '+hashlib.sha256(part).hexdigest()+'\n'+part.decode())
 with (R/'private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.relative_to(R).as_posix(),'line_start':a+1,'line_end':z,'byte_start':start,'byte_end':stop,'sha256':hashlib.sha256(part).hexdigest(),'parser':'bytes.splitlines(keepends=True)','coverage':'Displayed exact selected mathematics; tool truncation must be recovered separately.'})+'\n')
