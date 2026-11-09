import pathlib,json,hashlib,zipfile,re,datetime
D=pathlib.Path(__file__).resolve().parents[1]
modules=['Definitions','Arithmetic','Certificate']+['EdgeRows'+str(i) for i in range(8)]+['Endpoint']
audit=(D/'logs/lean-audit-r2.log').read_text()
assert 'sorryAx' not in audit and 'error:' not in audit
groups=[line.split("depends on axioms:",1)[1].strip().strip("[]") for line in audit.splitlines() if "depends on axioms:" in line]
used={a.strip() for g in groups for a in g.split(',') if a.strip()}
assert used == {'propext','Classical.choice','Quot.sound'}, used
names=json.loads((D/'outputs/local-declarations.json').read_text())
for m in modules:
 s=(D/f'lean/{m}.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
 for label in ['replay-'+m,'leanchecker-'+m]:
  if label == "leanchecker-Definitions": label = "leanchecker-Definitions-r2"
  assert json.loads((D/f'logs/{label}.receipt.json').read_text())['exit']==0,label
 src=(D/f'lean/{m}.lean').read_bytes();assert src==(D/f'replay/{m}.lean').read_bytes()
# Exactly one result entry per reservation and literal provenance binding.
rows=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text())
assert set(rows)==set(map(str,res['ids'])) and len(rows)==20
for i,row in rows.items():
 b=(D/f'raw/{i}.jsonl').read_bytes()
 assert hashlib.sha256(b).hexdigest()==row['provenance']['raw_sha256']
 assert b.endswith(b'\n')
 assert hashlib.sha256(row['statement'].encode()).hexdigest()==row['provenance']['statement_utf8_sha256']
status={'endpoint':'R162.not_conjecture349177 : ¬ R162.Conjecture349177','status':'kernel_checked_candidate_NOT_ACCEPTED','modules':modules,'strict_replay':True,'explicit_module_leanchecker':True,'all_local_declarations_audited':len(names),'axioms_allowed':['propext','Classical.choice','Quot.sound'],'limits':'RSS group watchdog 6 GiB; CPU120s/wall140s each call; taskset2 CPUs; lean -M3500 -j1; MALLOC_ARENA_MAX=2','trust_limits':['External prebuilt mathlib/package oleans trusted; no full upstream rebuild or source-to-olean attestation','leanchecker reuses Lean kernel; not a different foundation','RSS monitoring is sampled, not a cgroup or transient-peak guarantee'],'remaining_root_gates':['literal source interpretation / contracted nanostar bridge','independent mathematical, Lean fidelity and significance review','bounded prior-art clearance is not worldwide novelty','root acceptance and any manuscript requirements']}
(D/'lean-status.json').write_text(json.dumps(status,indent=2))
with zipfile.ZipFile(D/'proof-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for m in modules:z.write(D/f'lean/{m}.lean','lean/'+m+'.lean')
 for f in ['NANOSTAR.md','lean-status.json','outputs/totient-stage4-certificate.json','outputs/totient-independent.json','outputs/lean-label-order.json','outputs/local-declarations.json','scripts/run','scripts/lean-env','scripts/check-env','scripts/replay.sh']:
  z.write(D/f,f)
manifest={}
for p in sorted(D.rglob('*')):
 if p.is_file() and p.suffix not in ['.olean','.ilean','.ir'] and p.name!='manifest.json':
  manifest[str(p.relative_to(D))]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'manifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps(status,indent=2))
# Supplement the packet with the complete audit and a reproducible build guide.
with zipfile.ZipFile(D/'proof-source.zip','a',zipfile.ZIP_DEFLATED) as z:
 for f in ['BUILD.md','lean/Audit.lean','lean/Inventory.lean','scripts/audit.py','scripts/extract-replay.py','tools-bin/lean']:
  z.write(D/f,f)
# Final archive hash after supplements.
manifest['proof-source.zip']=hashlib.sha256((D/'proof-source.zip').read_bytes()).hexdigest()
(D/'manifest.json').write_text(json.dumps(manifest,indent=2))
