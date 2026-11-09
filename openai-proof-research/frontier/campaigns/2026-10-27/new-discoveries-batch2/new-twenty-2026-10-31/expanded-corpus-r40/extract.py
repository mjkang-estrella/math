import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; I=B/'lanes/pi-mathdb-full-corpus-inventory-r301'; R=json.loads((L/'reservation.json').read_text()); ids=set(R['ids']); H=lambda b:hashlib.sha256(b).hexdigest(); out={}; (L/'raw').mkdir(exist_ok=True)
m=json.loads((I/'manifest.json').read_text()); expected={x['path']:x['sha256'] for x in m['files']}
for f in sorted((I/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 b=f.read_bytes(); h=H(b); assert h==expected[str(f.relative_to(I))]
 for n,line in enumerate(b.splitlines(keepends=True),1):
  d=json.loads(line); k=d['mathdb_id']
  if k in ids:
   (L/'raw'/f'{k}.jsonl').write_bytes(line);out[str(k)]={'record':d,'provenance':{'chunk':str(f),'chunk_sha256':h,'line_one_based':n,'raw_sha256':H(line),'statement_sha256':H(d['statement'].encode()),'newline_preserved':line.endswith(b'\n')}}
assert len(out)==40
(L/'records.json').write_text(json.dumps(out,indent=2))
(L/'statements.txt').write_text('\n\n'.join(f"{k} {v['record']['title']}\n{v['record']['statement']}\nSOURCE {v['record']['source_url']} {v['record']['source_name']}" for k,v in out.items()))
# Search report/history only; corpus and routing/assignment metadata are not technical reviews.
pattern='|'.join(map(str,sorted(ids)))
p=subprocess.run(['rg','-l',pattern,str(B),'-g','*.md','-g','results.json','-g','review.json','-g','*ledger*.json','-g','!expanded-corpus-r40/**'],capture_output=True,text=True)
paths=[x for x in p.stdout.splitlines() if str(L) not in x]
(L/'history-id-paths.txt').write_text('\n'.join(paths)+'\n')
print((L/'statements.txt').read_text());print('HISTORY',len(paths), '\n'.join(paths[:20]))
