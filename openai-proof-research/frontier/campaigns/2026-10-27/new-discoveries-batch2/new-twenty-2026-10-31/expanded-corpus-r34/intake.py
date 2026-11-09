import json,hashlib,pathlib,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
sha=lambda x:hashlib.sha256(x).hexdigest()
r=json.loads((L/'reservation.json').read_text());ids=set(r['ids']); (L/'raw').mkdir(exist_ok=True)
out={}; chunks={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();chunks[str(p)] = sha(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] in ids:
   k=str(d['mathdb_id']);(L/'raw'/f'{k}.jsonl').write_bytes(line)
   out[k]={'record':d,'provenance':{'chunk':str(p),'chunk_sha256':sha(data),'one_based_line':n,'raw_sha256':sha(line),'statement_sha256':sha(d['statement'].encode()),'newline_preserved':line.endswith(b'\n')}}
assert set(map(int,out))==ids
(L/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(L/'statements.txt').write_text('\n\n'.join(f"{k} {v['record']['title']}\n{v['record']['statement']}\nSOURCE {v['record']['source_url']}\n{v['record']['references']}" for k,v in out.items()))
# IDs and literal titles; don't count metadata index mentions as prior mathematical review.
pat='|'.join(map(str,sorted(ids)))+'|'+'|'.join(__import__('re').escape(x['title']) for x in r['rows'])
p=subprocess.run(['rg','-n','-i','-e',pat,str(B),'--glob','*.md','--glob','*results.json','--glob','*ledger.json','--glob','!expanded-corpus-r34/**'],capture_output=True,text=True,timeout=80)
(L/'history-search.txt').write_text(p.stdout)
(L/'intake-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'chunks':chunks,'records':len(out),'search_returncode':p.returncode,'search_stderr':p.stderr},indent=2)+'\n')
print((L/'statements.txt').read_text())
