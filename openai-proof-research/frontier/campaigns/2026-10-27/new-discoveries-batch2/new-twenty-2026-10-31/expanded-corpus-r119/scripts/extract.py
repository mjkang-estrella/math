import pathlib,json,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]; C=D.parent; B=C.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text()); ids=set(r['ids']); out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); ch=sha(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  o=json.loads(line); i=o['mathdb_id']
  if i not in ids:continue
  (D/f'raw/{i}.jsonl').write_bytes(line)
  out[str(i)]={'mathdb_id':i,'title':o['title'],'statement':o['statement'],'source_url':o['source_url'],'provenance':{'chunk':str(p),'line_1based':n,'chunk_sha256':ch,'raw_sha256':sha(line),'statement_utf8_sha256':sha(o['statement'].encode())}}
assert len(out)==20
(D/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
patterns=[str(x) for x in sorted(ids)]+[x['title'] for x in out.values()]
(D/'scripts/history-patterns.txt').write_text('\n'.join(patterns)+'\n')
# Bound to prose and structured conclusions, excluding raw corpus and assignment metadata.
F=B.parents[2]
p=subprocess.run(['grep','-rniF','-f',str(D/'scripts/history-patterns.txt'),str(F),'--include=*.md','--include=*review*.json','--include=*results*.json','--include=*ledger*.json','--include=*disposition*.json','--include=*integration*.json','--exclude-dir=expanded-corpus-r119','--exclude-dir=.lake','--exclude-dir=corpus'],capture_output=True,text=True)
lines=[l[:600] for l in p.stdout.splitlines() if '/expanded-corpus-r119/' not in l]
(D/'history-matches.txt').write_text('\n'.join(lines)+'\n')
print(len(out),len(lines))
