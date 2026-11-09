import pathlib,json,hashlib,zipfile,re
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(map(int,r))==set(ids)
for i,o in r.items():
 assert o['credit']==0
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 if o['coverage_artifact']:assert (D/o['coverage_artifact']).exists()
 for sr in o['source_receipts']:
  if sr.get('status')==200:assert sha(pathlib.Path(sr['path']))==sr['sha256']
rep=json.loads((D/'replay/replay.json').read_text());assert len(rep['steps'])==5 and all(s['returncode']==0 for s in rep['steps'])
a=(D/'replay/Audit.log').read_text();assert 'AUDITED_LOCAL_DECLARATIONS|52' in a;assert 'sorryAx' not in a
for p in (D/'lean').glob('*.lean'):
 assert p.read_bytes()==(D/'replay'/p.name).read_bytes()
 s=re.sub(r'--[^\n]*|/\-.*?\-/','',p.read_text(),flags=re.S)
 s=re.sub(r'"(?:[^"\\]|\\.)*"','',s)
 # Declaration audit permits collectAxioms code; forbid actual unsound declaration/tactic tokens.
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
with zipfile.ZipFile(D/'350979-proof-source.zip') as z:assert set(z.namelist())=={'Circulant.lean','Bridge.lean','Endpoint.lean','Audit.lean'}
checks={'id_count':20,'all_credits':0,'strict_build_and_checker':'all five commands return zero','audited_local_declarations':52,'source_only_packet':True,'candidate':'350979','no_acceptance_claim':True,'coverage_limit':'Several finite models were not searched; see per-ID entries and SUMMARY.md.','script_sha256':sha(pathlib.Path(__file__))}
(D/'outputs/validation.json').write_text(json.dumps(checks,indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json' and '__pycache__' not in str(p)]
(D/'manifest.json').write_text(json.dumps({'files':files,'scope':'All lane files except this self-referential manifest and Python bytecode caches.'},indent=2)+'\n');print(json.dumps(checks,indent=2))
