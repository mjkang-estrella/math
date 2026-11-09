from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).parent
h=lambda b:hashlib.sha256(b).hexdigest()
res=json.loads((p/'reservation.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0];r=json.loads((p/'results.json').read_text());assert h((p/'reservation.json').read_bytes())==expected
assert len(r)==20 and set(r)==set(map(str,res['ids']))
for k,v in r.items():
 q=v['literal_provenance'];b=(p/q['raw_file']).read_bytes();assert b.endswith(b'\n');assert h(b)==q['raw_sha256'];assert json.loads(b)==v['full_parsed_record'];assert h(v['literal_statement'].encode())==q['statement_sha256_utf8'];f=Path(q['chunk']);assert h(f.read_bytes())==q['chunk_sha256'];assert f.read_bytes().splitlines(keepends=True)[q['line']-1]==b;assert v['credit']==0 and not v['accepted']
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation_hash':expected,'exact_keys':20,'raw_line_chunk_statement_checks':'PASS','zero_credit':True,'no_candidate':not (p/'CANDIDATE.md').exists(),'live_launched_fetch_sessions':0}
(p/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
files=sorted(f for f in p.rglob('*') if f.is_file() and f.name!='manifest.sha256')
(p/'manifest.sha256').write_text(''.join(h(f.read_bytes())+'  '+str(f.relative_to(p))+'\n' for f in files))
for line in (p/'manifest.sha256').read_text().splitlines():
 sha,name=line.split('  ',1);assert h((p/name).read_bytes())==sha
print(json.dumps(report,indent=2));print('Manifest files verified:',len(files))
