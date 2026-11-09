from pathlib import Path
import json,sys,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r217')
version,suffix,start,end=sys.argv[1:]
folder='Deforming-hypersymplectic-four-manifolds-to-hyperkahler-triples-'+({'oct':'October-7-2026','sep':'September-23-2026'}[version])
p=R/'private/preprints'/folder/suffix
b=p.read_bytes();lines=b.splitlines(keepends=True);a=int(start);z=min(int(end),len(lines)); selected=b''.join(lines[a-1:z])
assert len(selected)<=33000,'bounded reader requires smaller chunk'
print(f'{version}/{suffix} L{a}-{z} bytes [{sum(map(len,lines[:a-1]))},{sum(map(len,lines[:z]))}) of {len(b)}')
print(selected.decode())
with (R/'private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'path':str(p.relative_to(R)),'lines':[a,z],'bytes':[sum(map(len,lines[:a-1])),sum(map(len,lines[:z]))],'sha256':hashlib.sha256(selected).hexdigest(),'mode':'direct-complete-selected-lines'})+'\n')
