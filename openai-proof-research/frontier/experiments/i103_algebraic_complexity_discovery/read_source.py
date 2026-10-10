import json,sys,pathlib,hashlib
S=pathlib.Path('frontier/sources/i103_algebraic_complexity_discovery')
D=json.load(open('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'))
k,suffix=sys.argv[1:3];ds=[d for d in D if k in d['path'] and d['path'].endswith(suffix)]
assert len(ds)==1, [d['path'] for d in ds]
d=ds[0];b=pathlib.Path(d['local']).read_bytes();ls=b.decode().splitlines();a=int(sys.argv[3]) if len(sys.argv)>3 else 1;z=int(sys.argv[4]) if len(sys.argv)>4 else len(ls)
print(d['path'], 'LINES',len(ls),'RANGE',a,z)
for i in range(a-1,min(z,len(ls))):print(f'{i+1}: {ls[i]}')
r={'source':d['path'],'local':d['local'],'sha256':hashlib.sha256(b).hexdigest(),'first':a,'last':min(z,len(ls)),'convention':'Python str.splitlines(), 1-based inclusive','passage_sha256':hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()}
with open(S/'read-manifest.jsonl','a') as f:f.write(json.dumps(r)+'\n')
