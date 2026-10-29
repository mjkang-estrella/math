from pathlib import Path
import json,hashlib,datetime,urllib.request,subprocess
out=Path(__file__).parent;b=out/'frozen/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'; lanes=b/'lanes'
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':{k:json.loads((b/'ledger.json').read_text())[k] for k in ['accepted_count','total_accepted_count']},'trees':[]}
for p in [lanes/'sol-fresh-source-discovery-r57/sources/omega-D5.json',lanes/'sol-polyomino57-full-final-review-r1/live/omega-D5.json']:
 j=json.loads(p.read_text()); hits=[x for x in j['tree'] if any(s in x['path'].lower() for s in ['bessel','wronsk','sturmliouville'])]
 summary['trees'].append({'file':str(p.relative_to(out)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'sha':j.get('sha'),'truncated':j.get('truncated'),'entries':len(j['tree']),'hits':hits})
# Targeted immutable source reading, not an API retry or alternative head-discovery endpoint.
head='6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3'
paths=['D5/S3/Analytic/BesselRatioLogConcavity/Result.lean','Problems/karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity.md']
with (out/'http.jsonl').open('a') as log:
 for path in paths:
  url=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{path}';rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
  try:
   with urllib.request.urlopen(url,timeout=25) as r:
    data=r.read(2000000);name='omega-'+Path(path).name;(out/'public'/name).write_bytes(data);rec.update(status=r.status,file='public/'+name,sha256=hashlib.sha256(data).hexdigest(),headers=dict(r.headers),bytes=len(data))
  except Exception as e:rec['error']=str(e)
  log.write(json.dumps(rec)+'\n');print(path,rec.get('status',rec.get('error')))
(out/'scope-check.json').write_text(json.dumps(summary,indent=2))
print(json.dumps({**summary,'trees':[{**t,'hits':[x['path'] for x in t['hits']]} for t in summary['trees']]},indent=2))
