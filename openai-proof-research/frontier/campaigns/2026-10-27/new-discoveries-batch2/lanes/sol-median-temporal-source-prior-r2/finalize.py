from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((L/'binding-before.json').read_text())
after=[]
for r in before['files']:
 a=sha(Path(r['original']));b=sha(L/r['copy']);assert a==b==r['sha256']
 after.append(dict(original=r['original'],copy=r['copy'],sha256=a,match=True))
(L/'binding-after.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=after),indent=2))
access=[json.loads(s) for s in (L/'access.jsonl').read_text().splitlines()]
for r in access:
 if 'sha256' in r:
  p=L/r['derived'] if 'derived' in r else L/'sources'/r['name']
  assert sha(p)==r['sha256']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),guard=str(guard),guard_sha256=sha(guard),limits=dict(AS_bytes=512*1024*1024,groupRSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230),environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),retrievals=access,source_binding='binding-before.json',after_binding='binding-after.json',historical_reference_only='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',recommendation='bounded INVEST, acceptance/novelty HOLD',count_credit=0)
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
lines=['# SHA256 scientific binding and bounded access','', 'Local originals and selected copies:']
lines += [r['sha256']+'  '+r['copy'] for r in before['files']]
lines += ['', 'New HTTP bodies and extracted text (received-byte binding recorded before reading):']
lines += [r['sha256']+'  '+r.get('derived',r.get('name','')) for r in access if 'sha256' in r]
(L/'SOURCE-HASHES.md').write_text('\n'.join(lines)+'\n')
failures=['# Access failures and limits','', 'Inherited scientific failures preserved in freeze/02--FAILURES.md.']
failures += [r['utc']+' '+r['url']+' — '+r['failure'] for r in access if 'failure' in r]
failures += ['Project Euclid hydro.pdf: HTTP200 but Incapsula HTML challenge; no proof body, stopped.','Bing exact-title results irrelevant; arXiv temporal phrase results irrelevant; author query zero.','Journal accepted/published body not obtained. Four of six citing records metadata-only.','No current OpenAI git head or missing historical merge interval clearance. No denied-route retries.']
(L/'FAILURES.md').write_text('\n'.join(failures)+'\n')
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=manifest,excludes=['manifest.json','verification-receipt.json']),indent=2))
print('finalized',len(manifest),'files; original/copy bindings',len(after),'PASS')
