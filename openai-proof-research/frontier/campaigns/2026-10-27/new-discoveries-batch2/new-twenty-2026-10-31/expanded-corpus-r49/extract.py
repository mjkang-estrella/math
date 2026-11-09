import pathlib,json,hashlib,subprocess,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(900,900))
p=pathlib.Path(__file__).resolve().parent;b=p.parent.parent; inv=b/'lanes/pi-mathdb-full-corpus-inventory-r301'; r=json.loads((p/'reservation.json').read_text());ids=set(r['ids']);out={};(p/'raw').mkdir(exist_ok=True)
sha=lambda x:hashlib.sha256(x).hexdigest()
manifest=json.loads((inv/'manifest.json').read_text()); expected={x['path']:x['sha256'] for x in manifest['files']}
for f in sorted((inv/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes(); h=sha(data);assert h==expected[str(f.relative_to(inv))]
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] in ids:
   i=d['mathdb_id'];(p/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'record':d,'chunk':str(f),'line_1based':n,'chunk_sha256':h,'raw_sha256':sha(line),'statement_sha256':sha(d['statement'].encode()),'newline_preserved':line.endswith(b'\n')}
assert len(out)==40
(p/'literal-provenance.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
with (p/'statements.txt').open('w') as o:
 for i,d in out.items():o.write(f"\n## {i} {d['record']['title']}\n{d['record']['statement']}\nSOURCE {d['record']['source_url']} {d['record']['references']}\n")
# Historical notes: exact IDs and titles, excluding mechanical corpus/intake indexes and this lane.
cmd=['grep','-rniFI','--include=*.md','--include=*.json','--include=*.txt','--exclude=reservation.json','--exclude=mathdb-*','--exclude=screening-*','--exclude=routing-*','--exclude=coverage-*']
for row in r['rows']:cmd+=['-e',str(row['mathdb_id']),'-e',row['title']]
hraw=p/'history-raw.txt'
with hraw.open('wb') as fo:
 g=subprocess.Popen(cmd+[str(b)],stdout=subprocess.PIPE);c=subprocess.Popen(['cut','-c1-1200'],stdin=g.stdout,stdout=fo);g.stdout.close();c.wait(timeout=900);g.wait(timeout=900)
lines=[s for s in hraw.read_text(errors='replace').splitlines() if '/expanded-corpus-r49/' not in s and '/pi-mathdb-full-corpus-inventory-r301/' not in s]
(p/'history-search.txt').write_text('\n'.join(lines)+'\n');print('extracted',len(out),'history matches',len(lines))
# Input-hash integrity check of reservation-bound indexes (ledger is mutable context).
ih={}
for path,h in r['input_hashes'].items():
 q=pathlib.Path(path); now=sha(q.read_bytes()) if q.exists() else None; ih[path]={'reserved':h,'current':now,'match':now==h}
lp=pathlib.Path(r['mutable_campaign_ledger_snapshot']['path']); ih[str(lp)+' (mutable)']={'reserved':r['mutable_campaign_ledger_snapshot']['sha256'],'current':sha(lp.read_bytes()),'match':sha(lp.read_bytes())==r['mutable_campaign_ledger_snapshot']['sha256']}
(p/'input-integrity.json').write_text(json.dumps({'utc':datetime.datetime.utcnow().isoformat()+'Z','reservation_sha256':sha((p/'reservation.json').read_bytes()),'inputs':ih},indent=2)+'\n')
print(json.dumps(ih,indent=1))
