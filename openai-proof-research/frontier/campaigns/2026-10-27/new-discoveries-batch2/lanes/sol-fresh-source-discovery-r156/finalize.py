from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
history=json.loads((L/'history-receipt.json').read_text())
prov=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED; zero full proofs, zero nominees',source=dict(authors=['Shabnam Malik','Ahmad Mahmood Qureshi'],title='Hamiltonicity in directed Toeplitz graphs with s1 = 1 and s2 = 3',doi='10.47443/dml.2025.109',publication_date='2025-09-17',target='Conjecture 5.1, both parts, n>max(7,t)',quantifiers='Every even integer t>=16; every integer n>t with n mod4 in {1,2}; also n mod4=3 if t mod4=2'),retrievals=http,guard=dict(path=str(guard.resolve()),sha256=sha(guard),address_space_bytes=512*1024*1024,sampled_group_rss_bytes=512*1024*1024,cpu_seconds=210,wall_seconds=230,nominal_sample_ms=40,sampling_limit='Unsampled transient peaks not ruled out',environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')),registry=dict(omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',inherited_caps=['aa026->a19a:300 paths','a19a->490f:300 paths'],clearance=False),history=dict(receipt_sha256=sha(L/'history-receipt.json'),original_body_count=len(history['records']),changed_or_new=len(history['changed_or_new']),cutoff=None),limits=['No independent eligibility clearance','No full mathematical resolution','No universal seed or pumping proof','Current registry/source-facing actual body coverage bounded; no global semantic absence inference'],counts_unchanged=dict(additional=9,total=39,next=40),unauthorized_actions_performed=False)
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
excluded={'finalmanifest.json','manifest-verification.json','finalize.log','verify.log'}
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
manifest=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p)) for p in files],excluded=sorted(excluded),reason='Manifest and its verification receipt/logs excluded to avoid self-reference; all scientific payload and source bytes included.')
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('manifest payload paths',len(files))
