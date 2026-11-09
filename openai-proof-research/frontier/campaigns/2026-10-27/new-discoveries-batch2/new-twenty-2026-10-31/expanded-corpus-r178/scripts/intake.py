import pathlib,json,hashlib,re,subprocess
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent; ids=json.loads((D/'reservation.json').read_text())['ids']; out={}
h=lambda b:hashlib.sha256(b).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  if not any(str(i).encode() in line for i in ids):continue
  r=json.loads(line);i=r.get('mathdb_id',r.get('id'))
  if i not in ids:continue
  (D/f'raw/{i}.jsonl').write_bytes(line);out[str(i)]={'row':r,'chunk':str(p),'line':n,'chunk_sha256':h(data),'raw_sha256':h(line)}
(D/'extracted.json').write_text(json.dumps(out,indent=2)+'\n')
print('extracted',len(out))
for i,r in out.items():print(i,json.dumps(r['row'],ensure_ascii=False))
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 j=json.loads(p.read_text());(D/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_text(json.dumps(j,indent=2));print('CONTEXT',str(p),list(j) if isinstance(j,dict) else len(j))
pat='|'.join(map(str,ids))
p=subprocess.run(['rg','-n','-l',pat,str(D.parent),'-g','SUMMARY.md','-g','results.json','-g','review.json','-g','ledger.json'],capture_output=True,text=True)
(D/'outputs/history-paths.txt').write_text(p.stdout);print('history paths',p.stdout[:6000])
