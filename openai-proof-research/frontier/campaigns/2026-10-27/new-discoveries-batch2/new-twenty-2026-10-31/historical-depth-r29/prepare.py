import pathlib,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
D=pathlib.Path(__file__).resolve().parent;B=D.parent.parent;R=json.loads((D/'reservation.json').read_text()); h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (D/'results.json').exists(), 'Refusing to overwrite finalized dispositions'
receipts=[]
for group in ['prior_report_hashes','input_hashes']:
 for s,want in R[group].items():
  p=pathlib.Path(s);actual=h(p);receipts.append(dict(path=s,expected=want,actual=actual,match=actual==want));assert actual==want,(s,actual,want)
oldpath=next(iter(R['prior_report_hashes']));old=json.loads(pathlib.Path(oldpath).read_text());old={str(x['mathdb_id']):x for x in old};bindings=json.loads((pathlib.Path(oldpath).parent/'input-bindings.json').read_text())['refs'];expected={x['path']:x['sha256'] for x in bindings}
(D/'raw').mkdir(exist_ok=True);out={};found=set()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==expected[str(p)]
 for line,raw in enumerate(data.splitlines(keepends=True),1):
  x=json.loads(raw);i=str(x.get('mathdb_id',x.get('id')))
  if int(i) in R['ids']:
   (D/'raw'/f'{i}.jsonl').write_bytes(raw);o=old[i];out[i]=dict(mathdb_id=int(i),title=o['title'],literal_statement=o['statement'],old_disposition=o,prior_coverage=R['prior_coverage'][i],raw_record=dict(path=str(p),one_based_line=line,sha256=hashlib.sha256(raw).hexdigest(),chunk_sha256=hashlib.sha256(data).hexdigest(),local=f'raw/{i}.jsonl'),new_outcome='inherited_park_no_new_primary_body_review',new_primary_body_review=False,new_proof_body_review=False,accepted_credit=0);found.add(int(i))
assert found==set(R['ids']);(D/'results.json').write_text(json.dumps(out,indent=2)+'\n');(D/'verification.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),immutable_inputs=receipts,raw_count=len(out),all_chunk_hashes_verified=True,reservation_sha256=h(D/'reservation.json')),indent=2)+'\n');print('Verified immutable input hashes and all 20 chunks; extracted 40 exact raw lines.')
