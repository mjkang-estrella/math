from pathlib import Path
import json,urllib.request,hashlib,datetime
P=Path(__file__).resolve().parent
log=json.loads((P/'http.json').read_text())
jobs=[('poisson-structure.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/1b999d9fda71df7537b62327147496d64a6f66ef/Blueprint/D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.md'),('direction-bounds.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/1b999d9fda71df7537b62327147496d64a6f66ef/Blueprint/D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.md')]
# Inspect the actual cached live delta, not just r81's summary.
delta=json.loads((P/'sources/omega-delta').read_text());paths=[x['filename'] for x in delta.get('files',[])]
for i,path in enumerate(paths):jobs.append((f'live-delta-body-{i}.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/e50b06adbf73bc8eaa5ae905ad0d7b0d178fe377/'+path))
for name,url in jobs:
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:
   b=r.read(5*1024*1024);(P/'sources'/name).write_bytes(b);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:row['error']=str(e)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2))
heads={n:json.loads((P/'sources'/(n+'-head')).read_text())['sha'] for n in ['omega','openai']}
(P/'live-registry.json').write_text(json.dumps({'heads':heads,'delta_status':delta.get('status'),'total_commits':delta.get('total_commits'),'files':paths,'complete_file_list_claim':len(paths)<300,'limit':'Bounded path and selected-body screen; not semantic global absence.'},indent=2))
print(json.dumps(heads));print(paths)
for n in ['ledger.json','prior-campaign-context.json']:
 j=json.loads((P.parents[1]/n).read_text());print(n);print('\n'.join(str(x.get('number'))+' '+x['title'] for x in j['accepted']))
