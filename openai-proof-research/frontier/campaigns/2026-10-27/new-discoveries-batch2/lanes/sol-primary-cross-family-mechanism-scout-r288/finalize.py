import pathlib,json,hashlib,sys,time,shutil
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
rows=json.loads((L/'primary-bindings.json').read_text())
if sys.argv[1]=='finalize':
 failures=[r for r in rows if 'error' in r]
 dump(L/'failures.json',dict(acquisition_failures=failures,denied_routes_retried=False,parked=['GitHub API/raw/codeload/diff/patch','ScienceDirect','Google challenge routes','current proof registries previously denied'],notes=['Three 404s used malformed legacy IDs lacking category; corrected full canonical IDs succeeded. These were not 403/429/challenges.','Duplicate 2610.40342v1 hit across CO and NT attempted writing a read-only already frozen acquisition; failed before overwriting. Successful first binding remains authoritative.','Exact q*exp(z/2) positivity-factorization attempt fails at m=3.','No global novelty or registry clearance.']))
 good=[r for r in rows if 'sha256' in r]
 checks=[]
 for r in good:
  name=r['id'].replace('/','_')+'.pdf';p=L/'primary'/name
  assert sha(p)==r['sha256']==r['after_sha256']
  f=L/'frozen'/name
  existed=f.exists()
  if not existed:shutil.copyfile(p,f);f.chmod(0o444)
  checks.append(dict(id=r['id'],acquisition_hash=sha(p),frozen_copy_hash=sha(f),copy_existed_before_finalization=existed,unchanged=sha(p)==sha(f)==r['sha256']))
 dump(L/'checks/source-integrity.json',checks)
 admin=json.loads((L/'administrative-bindings.json').read_text())
 exclusions='\n'.join((L/r['snapshot']).read_text() for r in admin if r['snapshot'].endswith(('ledger.json','prior-campaign-context.json','SCOUTING.md')))
 dump(L/'checks/dedup.json',dict(exact_arxiv_id_occurrences={r['id']:exclusions.count(r['id'].split('v')[0]) for r in good},limit='Exact identifiers in administrative snapshots only; aliases and worldwide literature not cleared.'))
 dump(L/'provenance.json',dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),primary_acquisitions=len(good),mathematical_family_screens=16,ancillary_reports=2,qualified_nominees=0,counts=dict(additional=9,total=39,next=40),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',caps=dict(address_space_bytes=536870912,sampled_group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),limitations=['Current registries remain denied/parked; no retries.','No comprehensive citation-index audit.','2019 Fasi–Higham and Grosswald1978 original bodies unread.','Most primary screens read statements and nearby proof mechanism, not complete independent proof audits.','First acquisition hashes are pre/post extraction; local auxiliary copies for early acquisitions were created only at finalization.'],scientific_freeze='Each saved PDF made read-only before pdftotext or scientific reading; pre-extraction SHA and post-extraction SHA recorded.',retrieval='guarded Python urllib, normal TLS, no proxies or browsers; arXiv API discovery followed by version-pinned PDF',shared_writes=False,children=False,git_operations=False))
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 dump(L/'manifest.json',dict(algorithm='sha256',excludes=['manifest.json','verification-receipt.json'],files=files))
 print('manifest files',len(files),'successful unique bodies',len(good))
elif sys.argv[1]=='verify':
 m=json.loads((L/'manifest.json').read_text());bad=[s for s,h in m['files'].items() if not (L/s).exists() or sha(L/s)!=h]
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 unexpected=sorted(actual-set(m['files']))
 admin=json.loads((L/'administrative-bindings.json').read_text());ac=[]
 for r in admin:
  ac.append(dict(original=r['original'],original_unchanged=sha(pathlib.Path(r['original']))==r['before'],snapshot_unchanged=sha(L/r['snapshot'])==r['copy']))
 src=[]
 for r in rows:
  if 'sha256' not in r:continue
  name=r['id'].replace('/','_')+'.pdf'
  src.append(dict(id=r['id'],pass_hash=sha(L/'primary'/name)==sha(L/'frozen'/name)==r['sha256']==r['after_sha256'],pass_text=sha(L/'texts'/(r['id'].replace('/','_')+'.txt'))==r['text_sha256']))
 result=dict(manifest_sha256=sha(L/'manifest.json'),bad_files=bad,unexpected_files=unexpected,administrative=ac,primary_sources=src,pass_verification=not bad and not unexpected and all(x['original_unchanged'] and x['snapshot_unchanged'] for x in ac) and all(x['pass_hash'] and x['pass_text'] for x in src),meaning='Artifact integrity only; no mathematical proof or novelty PASS.')
 dump(L/'verification-receipt.json',result);print(json.dumps(result));assert result['pass_verification']
