import json,hashlib,zipfile
from pathlib import Path
r=Path(__file__).resolve().parents[1]
packet=r.parent/'middle-formal-r1/middle-source.zip'
assert hashlib.sha256(packet.read_bytes()).hexdigest()=='5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b'
with zipfile.ZipFile(packet) as z:
    for n in z.namelist():
        assert not Path(n).is_absolute() and '..' not in Path(n).parts
        assert (r/'extracted'/n).read_bytes()==z.read(n),n
rows=[json.loads(x) for x in (r/'extracted/audit.jsonl').read_text().splitlines()]
names={x['name'] for x in rows}
assert len(names)==len(rows)==252066
assert not {d for x in rows for d in x['deps_allowOpaque']}-names
local=[x for x in rows if x['local']]
assert len(local)==207
flags=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
allowed={'propext','Classical.choice','Quot.sound'}
for x in local:
    assert not any(x[k] for k in flags),x
    assert set(x['axioms'])<=allowed,x
endpoints=['g8_value',"g8_value'",'middle_g8_value',"middle_g8_value'",'mathdb_355217_connected',"mathdb_355217_connected'",'edgeless_two_literal_failure','G8_connected']
out={'packet_matches':True,'archive_members_unchanged':True,'audit_rows':len(rows),'local_rows':len(local),'missing_dependencies':0,'endpoint_axioms':{x['name']:x['axioms'] for x in local if x['name'].split('.')[-1] in endpoints},'upstream_metadata':{k:sum(x[k] for x in rows if not x['local']) for k in flags}}
assert len(out['endpoint_axioms'])==8
(r/'audit-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
