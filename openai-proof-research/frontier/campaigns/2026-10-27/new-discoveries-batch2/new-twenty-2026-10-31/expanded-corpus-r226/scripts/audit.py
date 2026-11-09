from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parents[1];ids=list(json.loads((L/'reservation.json').read_text())['ids']);out={}
for i in ids:
 hits=[]
 for p in L.parent.glob('expanded-corpus-r*/results.json'):
  if p.parent==L:continue
  try:r=json.loads(p.read_text())
  except Exception:continue
  if str(i) in r:hits.append({'path':str(p),'entry':r[str(i)]})
 out[str(i)]=hits
(L/'inputs/direct-historical-reviews.json').write_text(json.dumps(out,indent=2)+'\n')
registries=[]
for p in (L/'receipts').glob('2026*.json'):
 r=json.loads(p.read_text());u=r['url']
 if 'git/trees/' not in u:continue
 tree=json.loads((L/'receipts'/r['body']).read_text());pat=r'Trail.?Trap|Bajnok|Beatty|SpanningSet|Edoukou|Lando|Fomichev|Grunbaum|Grünbaum|SquaredPath|CutComplex|Petru|Skrek|Supersatur|TriangularEdge|Spider|Horoconvex|Zonotope|Observability|LocallyAnalytic|Semi.?algebraicRegular|UpwardFlag|DownwardFlag|SymmetricTheta'
 matches=[x['path'] for x in tree.get('tree',[]) if re.search(pat,x['path'],re.I)]
 registries.append(dict(url=u,receipt=p.name,sha=tree.get('sha'),truncated=tree.get('truncated'),matches=matches))
(L/'inputs/registry-screen.json').write_text(json.dumps(registries,indent=2)+'\n')
for r in registries:print(r['url'],r['sha'],r['truncated'],'\n'+'\n'.join(r['matches'])[:5000])
# Statement hashes use exact UTF-8 string as stored, with no normalization.
prov=json.loads((L/'inputs/provenance.json').read_text());rows=json.loads((L/'inputs/statements.json').read_text())
for i,r in rows.items():prov[i]['statement_sha256']=hashlib.sha256(r['statement'].encode()).hexdigest()
(L/'inputs/provenance-with-statements.json').write_text(json.dumps(prov,indent=2)+'\n')
print('direct history', {i:len(h) for i,h in out.items()})
