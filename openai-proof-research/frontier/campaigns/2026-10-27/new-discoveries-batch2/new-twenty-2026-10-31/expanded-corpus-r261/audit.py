import pathlib, json, hashlib, resource, subprocess, re, datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
P=pathlib.Path(__file__).resolve().parent; project=P.parents[5]; d=json.loads((P/'extracted.json').read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
for k,v in d.items():
 r=v['record']; pats=[r'\b'+k+r'\b',re.escape(r['title']),re.escape(r['source_url'].rsplit('/',1)[-1])]
 cmd=['rg','-n','-i','-e','|'.join(pats),'-g','*.md','-g','*.json','-g','*.txt','-g','*.yml','-g','!reservation.json','-g','!extracted.json','-g','!results.json','-g','!history*','-g','!MANIFEST*','-g','!*tree*','-g','!*manifest*','-g','!*receipts*','-g','!mathdb-normalized*',str(project)]
 cp=subprocess.run(cmd,capture_output=True,timeout=30)
 lines=cp.stdout.decode(errors='replace').splitlines(); relevant=[s for s in lines if str(P)+'/' not in s]
 (P/f'historical-context-{k}.txt').write_text('\n'.join(s[:1800] for s in relevant[:150])+'\n')
 v['history']={'command':cmd,'exit':cp.returncode,'raw_output_sha256':sha(cp.stdout),'match_lines':len(relevant),'saved_line_cap':150,'saved_character_per_line_cap':1800}
 v['raw_provenance']['statement_sha256']=sha(r['statement'].encode())
 print(k,r['title'],'history lines',len(relevant))
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/STATUS.md']:
 f=project/rel
 if f.exists():
  b=f.read_bytes()
  with (P/'context-read-receipts.jsonl').open('a') as out:out.write(json.dumps({'path':str(f),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':sha(b),'bytes':len(b)})+'\n')
  if f.name=='ledger.json':
   obj=json.loads(b); print('Ledger',rel,'keys',list(obj)[:20])
(P/'audited-extraction.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
for k,v in d.items():print('\n',k,v['record']['statement'])
