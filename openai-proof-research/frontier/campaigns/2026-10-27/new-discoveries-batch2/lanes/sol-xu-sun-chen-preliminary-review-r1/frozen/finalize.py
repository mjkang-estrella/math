from pathlib import Path
import hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
# The finalizer itself is launched under this unchanged guard; children inherit caps.
r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,check=True)
(L/'checks.json').write_text(r.stdout)
history=json.loads((L/'history-receipt.json').read_bytes())
# Read only changed original reports and contexts for final disposition reconciliation.
for p,h,z in history['changed']:
 b=(L.parents[5]/p).read_bytes();assert sha(b)==h
for n in ['context-ledger.json','context-prior-campaign-context.json']:json.loads((L/n).read_bytes())
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='zero qualifying discoveries; routine adaptation exclusion recommended',guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_MiB=512,sampled_group_RSS_MiB=512,CPU_s=210,wall_s=230,nominal_sampling_ms=40,limits='between-sample RSS spikes not ruled out'),http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()],history=dict(receipt_sha256=sha((L/'history-receipt.json').read_bytes()),records=len(history['records']),changed=len(history['changed'])),registry_heads={n:json.loads((L/'sources'/f'{n}-head.json').read_bytes())['sha'] for n in ['omega','openai']},inherited_gaps=['two older 300-path comparison caps','lexical path screen is not semantic registry clearance'],protocol_deviations=['initial read-only inventory not guarded','premature missing-file conversions and read corrected after HTTP completed'],scientific_status='ordinary proof closed for Conjectures2/3; routine source-method adaptation, no eligibility clearance; no formal claim'))
excluded={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
save('scientific-freeze.json',dict(files=files,scope='All final payload bytes; excludes only manifests and verification receipt'))
files['scientific-freeze.json']=sha((L/'scientific-freeze.json').read_bytes())
save('finalmanifest.json',dict(files=files))
r=subprocess.run([sys.executable,str(L/'verify.py')],capture_output=True,text=True,check=True)
save('manifest-verification.json',dict(status='PASS',output=r.stdout,scientific_paths=len(files)-1,manifest_paths=len(files),finalmanifest_sha256=sha((L/'finalmanifest.json').read_bytes())))
print(r.stdout)
