from pathlib import Path
import json,hashlib,os,re,datetime
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.load(open(D/'extracted.json'));r=json.load(open(D/'results.json'));res=json.load(open(D/'reservation.json'))
assert len(r)==20 and set(r)==set(map(str,res['ids']))
for i,o in x.items():
 p=o['provenance'];b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==p['raw_sha256'];assert sha(o['statement'].encode())==p['statement_utf8_sha256']
 # Re-read original exact chunk/line without mutation.
 c=Path(p['chunk']).read_bytes();assert sha(c)==p['chunk_sha256'];assert c.splitlines(keepends=True)[p['line_1based']-1]==b
for p in (D/'sources').glob('*.receipt.json'):
 a=json.load(open(p))
 if 'sha256' in a:assert sha(Path(a['path']).read_bytes())==a['sha256']
for n in ['extracted-build','extracted-audit','extracted-checker']:
 a=json.load(open(D/f'logs/{n}.receipt.json'));assert a['returncode']==0 and a['cap_reason'] is None
s=(D/'fresh-extracted/Comb.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
assert (D/'formal/Comb.lean').read_bytes()==(D/'fresh-extracted/Comb.lean').read_bytes()
audit=(D/'logs/extracted-audit.log').read_text();count=re.search(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',audit);assert count and int(count[1])==83
# Audit rejects unsafe/new axioms and disallowed transitive axioms for EVERY local declaration.
assert 'error:' not in audit
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd==D or D in cwd.parents:
   # This validator's launching shell is foreground; report other workers.
   if 'scripts/validate.py' not in cmd and 'exec_command' not in cmd:active.append({'pid':int(p.name),'cmd':cmd})
 except (OSError,PermissionError):pass
v={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'id_entries':20,'raw_line_and_chunk_hashes_verified':True,'http_receipt_hashes_verified':True,'strict_zip_extracted_build':'PASS','leanchecker':'PASS','all_local_declarations_audited':83,'allowed_transitive_axioms':['propext','Classical.choice','Quot.sound'],'source_endpoint':'Comb373367.mathdb_373367_false','credit':0,'recommendation':'Exclude373367 as routine consequence of Tan–Teh2022 Theorem2.6; root adjudicates. No accepted discoveries.','other_lane_cwd_processes':active,'dependency_trust':'Cached upstream oleans; no full rebuild/source-olean attestation.'}
(D/'outputs/validation.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
