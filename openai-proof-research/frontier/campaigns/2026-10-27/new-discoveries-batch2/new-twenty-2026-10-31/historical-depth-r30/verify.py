import pathlib,json,hashlib,datetime
W=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((W/'reservation.json').read_text());d=json.loads((W/'results.json').read_text());assert set(d)==set(map(str,r['ids']));assert len(d)==40
for p,h in {**r['prior_report_hashes'],**r['input_hashes']}.items():assert H(pathlib.Path(p).read_bytes())==h,p
old={}
for p in r['prior_report_hashes']:
 for x in json.loads(pathlib.Path(p).read_text()):old[str(x['mathdb_id'])]=x
cache={}
for k,x in d.items():
 assert x['old_disposition']==old[k];assert x['accepted_credit']==x['discovery_credit']==0
 p=x['corpus_path']
 if p not in cache:cache[p]=pathlib.Path(p).read_bytes();assert H(cache[p])==x['chunk_sha256']
 raw=cache[p].splitlines(keepends=True)[x['line_one_based']-1];assert raw==(W/'raw'/f'{k}.jsonl').read_bytes();assert H(raw)==x['raw_sha256'];assert json.loads(raw)==x['record'];assert x['exact_scope']==x['record']['statement'];assert H(x['exact_scope'].encode())==old[k]['statement_sha256']
 canonical=json.dumps(x['record'],ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();assert H(canonical)==old[k]['canonical_record_sha256']
 for s in x['source_receipts']:
  q=W/s['receipt'];a=json.loads(q.read_text());assert H(q.read_bytes())==s['receipt_sha256'];stem=q.name.removesuffix('.receipt.json');assert H((q.parent/(stem+'.pdf')).read_bytes())==s['source_sha256'];assert H((q.parent/(stem+'.txt')).read_bytes())==s['text_sha256']
assert not set(d)&set(r['excluded_ids']);screen=json.loads((W/'registry-screen.json').read_text());assert H(pathlib.Path(screen['reused_tree_path']).read_bytes())==screen['reused_tree_sha256']
manifest=json.loads((W/'manifest.json').read_text())
for p,h in manifest.items():assert H((W/p).read_bytes())==h,p
actual={str(p.relative_to(W)) for p in W.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification.json','verify.log']};assert actual==set(manifest)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=True,ids=40,raw_lines=40,new_related_primary_ids=sum(x['new_primary_body_review'] for x in d.values()),new_selected_proof_ids=sum(x['new_proof_section_review'] for x in d.values()),original_workshop_body_ids=0,credit=0,local_files=len(manifest),limits='2 CPU affinity; AS1GiB CPU45s wall60s',scope='Byte/structure/assignment verification; not an independent mathematical review, formal certificate or acceptance.')
(W/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
