import pathlib,json,hashlib,resource,subprocess,re
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
o=pathlib.Path(__file__).resolve().parent;h=lambda data:hashlib.sha256(data).hexdigest();x=json.loads((o/'results.json').read_text());r=json.loads((o/'reservation.json').read_text());assert set(x)==set(map(str,r['ids'])) and len(x)==40
for i,v in x.items():
 raw=(o/'raw'/f'{i}.jsonl').read_bytes();q=v['provenance'];assert raw.endswith(b'\n') and h(raw)==q['raw_sha256'];assert json.loads(raw)==v['record'];assert h(v['record']['statement'].encode())==q['statement_utf8_sha256'];assert v['credit']==0
for receipt in ['source-receipts.json','extra-source-receipts.json']:
 for v in json.loads((o/receipt).read_text()):
  if v.get('status')==200:assert h((o/v['file']).read_bytes())==v['sha256']
# Earlier campaigns: bounded exact-title search, no historical tree copying.
q=subprocess.run(['rg','-n','--max-columns','700','-e','|'.join(re.escape(v['record']['title']) for v in x.values()),str(o.parents[3]),'--glob','*.md','--glob','*results.json','--glob','*review.json'],capture_output=True,text=True,timeout=40)
lines=[s for s in q.stdout.splitlines() if '/new-discoveries-batch2/' not in s];(o/'older-history-title-matches.txt').write_text('\n'.join(lines)+'\n')
assert not lines
for v in x.values():v['history_check']['older_campaigns']='Also checked older campaigns md/*results.json/*review.json by exact-word ID and exact title; no matches. Not all unindexed files/bodies/history checked.'
(o/'results.json').write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
receipt={'exact_id_key_count':len(x),'all_raw_hashes_and_newlines_verified':True,'statement_hash_encoding':'SHA256 of literal decoded statement UTF8, no normalization','successful_download_hashes_verified':True,'reservation_input_bindings':'environment.json; all five match','primary_context_ids':[358935,358937,359147,359148,359262,359653,359711,359719,359721],'substantive_target_selected_body_ids':[358937,359147,359148,359262,359653,359711,359719,359721],'literal_only':31,'new_lean_endpoints':0,'credit':0,'no_background_jobs':'all launched sessions completed; no jobs detached','limits':'expensive scripts taskset CPUs0,1; 2GiB address-space RLIMIT; finite CPU/wall caps; see SUMMARY. No aggregate RSS/cgroup or full upstream rebuild claim.'}
(o/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
