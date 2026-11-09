import json,pathlib,hashlib,datetime
W=pathlib.Path(__file__).resolve().parent; B=W.parent.parent
H=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((W/'reservation.json').read_text()); audit=[];old={}
for p,h in {**r['prior_report_hashes'],**r['input_hashes']}.items():
 q=pathlib.Path(p);actual=H(q.read_bytes());audit.append(dict(path=p,expected=h,actual=actual,match=actual==h));assert actual==h,(p,actual)
for p in r['prior_report_hashes']:
 for x in json.loads(pathlib.Path(p).read_text()):
  if x['mathdb_id'] in r['ids']:old[str(x['mathdb_id'])]=x
cor=B/'lanes/pi-mathdb-full-corpus-inventory-r301';m=json.loads((cor/'manifest.json').read_text()); found={};(W/'raw').mkdir(exist_ok=True)
for f in m['files']:
 if not f['path'].startswith('corpus/mathdb-normalized-chunk-'):continue
 p=cor/f['path'];data=p.read_bytes();assert H(data)==f['sha256'];audit.append(dict(path=str(p),sha256=H(data),match=True))
 for n,line in enumerate(data.splitlines(keepends=True),1):
  x=json.loads(line);k=str(x['mathdb_id'])
  if int(k) not in r['ids']:continue
  assert H(x['statement'].encode())==old[k]['statement_sha256'];canonical=json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();assert H(canonical)==old[k]['canonical_record_sha256']
  (W/'raw'/f'{k}.jsonl').write_bytes(line);found[k]=dict(record=x,corpus_path=str(p),line_one_based=n,raw_sha256=H(line),chunk_sha256=H(data),raw_includes_newline=line.endswith(b'\n'),old_report=r['prior_coverage'][k]['report'],old_disposition=old[k],new_primary_body_review=False,new_proof_section_review=False,new_outcome='inherited_hold_preserved_not_new_primary_review',accepted_credit=0)
assert set(found)==set(map(str,r['ids']));assert not set(found)&set(r['excluded_ids'])
(W/'results.json').write_text(json.dumps(found,indent=2,ensure_ascii=False)+'\n');(W/'binding-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
context=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',W.parent/'ledger.json',B/'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',B/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 d=json.loads(p.read_text());context.append(dict(path=str(p),sha256=H(p.read_bytes()),bytes=p.stat().st_size));
(W/'context-bindings.json').write_text(json.dumps(context,indent=2)+'\n')
print('Verified immutable reports/inputs, 20 corpus chunks, 40 raw lines and prior statement/canonical hashes; excluded IDs disjoint.')
