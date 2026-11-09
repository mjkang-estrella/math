import pathlib,json,hashlib,re,zipfile,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text());v=json.loads((D/'results.json').read_text());assert len(v)==40 and set(v)==set(map(str,r['ids']))
for i,o in v.items():
 b=(D/o['raw_file']).read_bytes();p=o['provenance'];assert b.endswith(b'\n') and sha(b)==p['raw_sha256'];raw=json.loads(b);assert raw['mathdb_id']==int(i);assert sha(o['statement'].encode())==p['statement_utf8_sha256'];assert raw['statement']==o['statement'];assert sha((D/o['primary_file']).read_bytes())==o['primary_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text())
 if o.get('status')==200:assert sha(pathlib.Path(o['path']).read_bytes())==o['sha256']
a=(D/'outputs/fresh-audit.log').read_text();names=re.findall(r'AXIOM_AUDIT ([^:]+):',a);assert len(names)==45 and len(set(names))==45;assert 'UNAPPROVED' not in a
s=(D/'lean/SignedMass.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
res=json.loads((D/'outputs/replay.json').read_text());assert set(res)=={'compile','audit','checker'} and all(o['exit']==0 for o in res.values())
with zipfile.ZipFile(D/'proof-packet.zip') as z:assert z.read('SignedMass.lean')==(D/'lean/SignedMass.lean').read_bytes();assert z.read('Audit.lean')==(D/'lean/Audit.lean').read_bytes()
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':len(v),'raw_lines_verified':40,'all_local_declarations_audited':len(names),'strict_rebuild':res,'accepted_credit':0,'campaign_count_unchanged':'7/20 beyond39','checks':'raw newline/hash, literal, primary receipts, packet byte equality, forbidden-proof scan, allowed axiom program, replay exits'}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'}
(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
