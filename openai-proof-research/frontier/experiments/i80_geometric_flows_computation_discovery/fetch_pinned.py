from pathlib import Path
import json,hashlib,urllib.request,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i80_geometric_flows_computation_discovery'
m=json.loads((S/'source-manifest.json').read_text());records=[]
wanted=[('RV','build/addressed.tex'),('RV','build/main.tex'),('FP','build/analytic-appendix.tex'),('GS','build/analytic-imports.tex'),('FS','build/main.tex'),('HY','build/sections/11-endpoint.tex'),('RH','build/sections/06-barriers.tex')]
for family,suffix in wanted:
 e=next(x for x in m if x['family']==family and x['path'].endswith(suffix) and (family!='HY' or 'October' in x['path']))
 req=urllib.request.Request(e['raw_url'],headers={'User-Agent':'I80 mathematical research provenance'})
 with urllib.request.urlopen(req,timeout=45) as r:
  b=r.read();record=dict(url=e['raw_url'],final_url=r.url,status=r.status,headers=dict(r.headers),retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat())
 assert hashlib.sha256(b).hexdigest()==e['sha256']
 q=S/'fresh-raw'/family/suffix;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 record.update(path=str(q.relative_to(R)),upstream_reference=e['path'],git_blob=e['git_blob'],sha256=e['sha256'],bytes=len(b));records.append(record)
(S/'pinned-requests.json').write_text(json.dumps(records,indent=2)+'\n');print('fresh pinned responses',len(records))
