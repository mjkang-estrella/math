import json,pathlib,hashlib,re
r=json.load(open('results.json'));res=json.load(open('reservation.json'));assert len(r)==20 and set(r)==set(map(str,res['ids']))
for k,v in r.items():
 p=pathlib.Path(v['provenance']['raw_path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==v['provenance']['raw_sha256'];assert p.read_bytes().endswith(b'\n')
assert 'AUDITED_LOCAL_DECLARATIONS 24' in pathlib.Path('outputs/replay-final-axioms.log').read_text()
assert not any(x in pathlib.Path('outputs/replay-final-axioms.log').read_text() for x in ['sorryAx','error:'])
assert pathlib.Path('outputs/verification-status.txt').read_text().strip()=='All final checks exited 0'
for p in ['TorusPMD.lean']:
 s=pathlib.Path(p).read_text();assert not re.search(r'\b(sorry|admit|native_decide|ofReduceBool|unsafe|axiom)\b',s)
files=['SUMMARY.md','PROOF.md','results.json','TorusPMD.lean','AuditAll.lean','lean-packet.tar.gz']+[str(p) for p in pathlib.Path('sources').glob('*') if p.is_file()]+[str(p) for p in pathlib.Path('scripts').glob('*') if p.is_file()]
json.dump({p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in files},open('outputs/artifact-hashes.json','w'),indent=2)
print('PASS: exactly 20 reserved IDs; raw hashes and final replay/audit status verified')
