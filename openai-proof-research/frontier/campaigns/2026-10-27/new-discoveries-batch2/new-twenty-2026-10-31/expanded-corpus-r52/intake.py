import pathlib,json,hashlib,subprocess,datetime
R=pathlib.Path(__file__).resolve().parent; B=R.parent.parent; C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'; h=lambda b:hashlib.sha256(b).hexdigest(); d=json.loads((R/'reservation.json').read_text()); out={}; checks=[]
for s,x in d['input_hashes'].items():
 p=pathlib.Path(s); actual=h(p.read_bytes()); checks.append({'path':s,'expected':x,'actual':actual,'match':x==actual,'mutable':p==B/'ledger.json'})
manifest=json.loads((C/'manifest.json').read_text()); (R/'raw').mkdir(exist_ok=True)
for f in manifest['files']:
 if not f['path'].startswith('corpus/'):continue
 p=C/f['path']; raw=p.read_bytes(); assert h(raw)==f['sha256']
 for n,line in enumerate(raw.splitlines(keepends=True),1):
  row=json.loads(line); i=row['mathdb_id']
  if i not in d['ids']:continue
  (R/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'record':row,'provenance':{'chunk':str(p),'line_one_based':n,'chunk_sha256':h(raw),'raw_line_sha256':h(line),'statement_utf8_sha256':h(row['statement'].encode())}}
assert len(out)==40
(R/'records.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');(R/'input-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(R/'statements.txt').write_text('\n\n'.join(f"{i} {v['record']['title']}\n{v['record']['statement']}\nSOURCE {v['record']['source_url']}\n{v['record']['source_name']}" for i,v in out.items()))
print('40 extracted; immutable checks',checks)
