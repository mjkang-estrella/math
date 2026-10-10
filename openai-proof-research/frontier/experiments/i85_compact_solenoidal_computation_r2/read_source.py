from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i85_compact_solenoidal_computation_r2'
manifest=json.loads((R/'frontier/sources/i80_geometric_flows_computation_discovery/source-manifest.json').read_text())
fam,suffix=sys.argv[1:3]
m=[x for x in manifest if x['family']==fam and x['path'].endswith(suffix)]
if len(m)!=1: raise SystemExit('ambiguous '+str([x['path'] for x in m]))
x=m[0];p=R/x['path'];b=p.read_bytes();lines=b.splitlines(keepends=True)
a=int(sys.argv[3]) if len(sys.argv)>3 else 1
z=int(sys.argv[4]) if len(sys.argv)>4 else len(lines)
z=min(z,len(lines));fragment=b''.join(lines[a-1:z])
print(x['upstream_path'],a,z)
print(fragment.decode(),end='')
record=dict(x,start=a,end=z,total_lines=len(lines),passage_sha256=hashlib.sha256(fragment).hexdigest())
with (S/'reading-deliveries.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
