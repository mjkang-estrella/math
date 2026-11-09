import pathlib,json,hashlib,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
w=pathlib.Path(__file__).resolve().parent; batch=w.parent.parent; corpus=batch/'lanes/pi-mathdb-full-corpus-inventory-r301'; r=json.loads((w/'reservation.json').read_text()); ids=set(r['ids']); (w/'raw').mkdir(exist_ok=True); out={}; manifest=json.loads((corpus/'manifest.json').read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
for ent in manifest['files']:
 if not ent['path'].startswith('corpus/mathdb-normalized-chunk-'):continue
 p=corpus/ent['path'];data=p.read_bytes();assert sha(data)==ent['sha256']
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line); i=d.get('id',d.get('mathdb_id'))
  if i not in ids:continue
  (w/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'chunk':str(p),'line_one_based':n,'chunk_sha256':sha(data),'raw_sha256':sha(line),'statement_sha256':sha(d.get('statement','').encode()),'record':d}
assert len(out)==40
(w/'provenance.json').write_text(json.dumps(out,indent=2)+'\n')
(w/'statements.txt').write_text('\n\n'.join(i+' '+json.dumps(d['record'],ensure_ascii=False) for i,d in out.items()))
patterns='|'.join(map(str,sorted(ids))); proc=subprocess.run(['rg','-l','--glob','*.md','--glob','results.json','--glob','*review*.json',patterns,str(batch)],capture_output=True,text=True,timeout=45); paths=[p for p in proc.stdout.splitlines() if '/expanded-corpus-r43/' not in p];(w/'history-paths.txt').write_text('\n'.join(paths)+'\n')
print('Extracted',len(out),'history files',len(paths))
