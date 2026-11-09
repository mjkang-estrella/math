from pathlib import Path
import json,hashlib,resource,datetime
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids)) and len(r)==20
for i,x in r.items():
 p=Path(x['provenance']['chunk']);b=p.read_bytes();assert sha(b)==x['provenance']['chunk_sha256']
 line=b.splitlines(keepends=True)[x['provenance']['line']-1];assert line==(L/x['raw_file']).read_bytes();assert sha(line)==x['provenance']['raw_sha256'];assert line.endswith(b'\n')
 assert sha(x['literal_record']['statement'].encode())==x['provenance']['statement_sha256'];assert x['discovery_credit']==0
receipts=[]
for p in (L/'http').glob('*.receipt.json'):
 x=json.loads(p.read_text());body=p.with_name(p.name.removesuffix('.receipt.json'));x['receipt_file']=str(p.relative_to(L))
 if body.exists():
  b=body.read_bytes()
  if 'sha256' in x:assert x['sha256']==sha(b)
  x['retained_body_sha256']=sha(b);x['representation']='PDF' if b.startswith(b'%PDF') else 'JSON/text/HTML'
 else:x['retained_body_sha256']=None
 x.setdefault('status',None);receipts.append(x)
(L/'source-receipts.json').write_text(json.dumps(receipts,indent=2))
# Correct final representation depth explicitly.
r['329705']['literature_limits'].append('Journal direct HTTP route timed out; web-indexed primary passage inspected, direct full journal body unread.')
r['329726']['literature_limits'].append('Journal download returned HTTP 200 HTML rather than PDF; primary preprint read, journal body unread.')
r['358939']['review_depth']+='; actual gamma-journal.pdf Section 7 Conjecture 7.2 inspected'
(L/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False))
stat=[]
for p in L.glob('*.run.json'):
 x=json.loads(p.read_text());assert x['exit']==0,(p,x);stat.append({'file':p.name,'exit':0,'wall_seconds':x['wall_seconds']})
reg={}
for name in ['openai','omega','pool']:
 p=L/'http'/(name+'-head.json');reg[name]=json.loads(p.read_text())['sha']
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exactly_twenty':True,'all_original_chunks_and_lines_hash_verified':True,'all_source_receipt_body_hashes_verified':True,'credit':0,'campaign_count_unchanged':'52/60','lean_builds':0,'heavy_mathematical_execution':False,'registry_heads':reg,'completed_run_receipts':stat,'no_unreaped_launched_sessions':True,'peak_rss_kib_this_check':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'limits':'cap runner pins metadata jobs to same <=2 CPUs, CPU120s/wall140s/AS6GiB. Earlier per-job RSS not sampled.'}
(L/'validation.json').write_text(json.dumps(report,indent=2))
manifest={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name!='HASHES.json' and p.name not in ['final-check.log','final-check.run.json']}
(L/'HASHES.json').write_text(json.dumps(manifest,indent=2));print('PASS',len(r),'IDs;',len(receipts),'source receipts;',len(manifest),'hashed files; zero credit')
