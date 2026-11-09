import pathlib,json,hashlib,zipfile,re
D=pathlib.Path(__file__).resolve().parents[1];R=json.loads((D/'results.json').read_text());assert len(R)==20
h=lambda b:hashlib.sha256(b).hexdigest()
for i,x in R.items():
 raw=(D/x['raw_file']).read_bytes();assert raw.endswith(b'\n') and h(raw)==x['provenance']['raw_sha256'];assert h(x['literal_statement'].encode())==x['provenance']['statement_sha256']
 assert json.loads(raw)['mathdb_id']==int(i)
source=(D/'lean/Interpolation.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',source)
assert (D/'fresh-replay/Interpolation.lean').read_bytes()==(D/'lean/Interpolation.lean').read_bytes()
for name in ['fresh-compile','kernel-check','audit']:
 x=json.loads((D/f'logs/{name}.receipt.json').read_text());assert x['returncode']==0 and x['cap_reason'] is None
manifest={'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','source_sha256':h(source.encode()),'literal_endpoint':'OrientableTotalDomination.conjecture_true','module':'Interpolation','strict_rebuild':'PASS','explicit_module_leanchecker':'PASS','all_local_declarations':38,'all_local_axiom_audit':'PASS','axioms':['propext','Classical.choice','Quot.sound'],'cache_trust':'read-only pinned oleans; no full upstream rebuild','independent_review':'PENDING','root_acceptance':'PENDING','credit':0}
(D/'lean/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(D/'Lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p,name in [(D/'lean/Interpolation.lean','Interpolation.lean'),(D/'lean/Audit.lean','Audit.lean'),(D/'lean/manifest.json','manifest.json'),(D/'REPLAY.md','REPLAY.md')]:z.write(p,name)
with zipfile.ZipFile(D/'Lean-packet.zip') as z:assert sorted(z.namelist())==['Audit.lean','Interpolation.lean','REPLAY.md','manifest.json']
report={'twenty_entries':True,'exact_raw_and_statement_hashes':True,'literal_lean_endpoint':manifest,'packet_sha256':h((D/'Lean-packet.zip').read_bytes()),'pending':'independent review, broader novelty/significance review, root acceptance','files':{str(p.relative_to(D)):h(p.read_bytes()) for p in [D/'results.json',D/'SUMMARY.md',D/'CANDIDATE.md',D/'outputs/registry-screen.json']}}
(D/'outputs/final-validation.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
