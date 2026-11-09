import json,hashlib,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r597'
def sig(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,r):
 s=sig(p);assert all(s[k]==r[k] for k in ['size','sha256']),str(p);return s
out=[]
check(I/'manifest.json',{'size':9547,'sha256':'99dbb14e5f76cdd68dc3393a39727e184e68079f69b471575ababab182582909'})
m=json.loads((I/'manifest.json').read_text()); expected={r['path'] for r in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(m['excluded_exact_paths'])
out.append(sig(I/'manifest.json'))
for r in m['files']:out.append(check(I/r['path'],r))
out.append(sig(I/'verification-receipt.json'))
for r in json.loads((I/'bindings.json').read_text()):
 out.extend([check(pathlib.Path(r[k]),r) for k in ['original','copy']]);assert pathlib.Path(r['original']).read_bytes()==pathlib.Path(r['copy']).read_bytes()
R=L/'pi-mathdb-full-corpus-inventory-r301';rm=json.loads((R/'manifest.json').read_text());print('R301 structure',[(k,type(v).__name__,len(v) if hasattr(v,'__len__') else '') for k,v in rm.items()]);print(json.dumps(rm,ensure_ascii=False)[:6500])
(P/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
chunks=[r for r in rm['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for r in chunks+rm['frozen_inputs']:out.append(check(R/r['path'],{'size':r['bytes'],'sha256':r['sha256']}))
extra=[L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md',L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json']
for lane in ['sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r542']:
 for p in (L/lane).glob('*'):
  if p.is_file() and ('fail' in p.name or p.name=='SUMMARY.md'):extra.append(p)
for p in extra:
 if p.exists():out.append(sig(p))
(P/'flat-bindings.json').write_text(json.dumps(list({r['path']:r for r in out}.values()),indent=2)+'\n')
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids']);rows=[]
for r in chunks:
 for n,line in enumerate((R/r['path']).open(),1):
  d=json.loads(line)
  if d['mathdb_id'] in ids:rows.append({'mathdb_id':d['mathdb_id'],'chunk':str(R/r['path']),'line':n,'statement':d['statement'],'statement_sha256':hashlib.sha256(d['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':d})
assert len(rows)==50
rows.sort(key=lambda r:r['mathdb_id']);(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for r in rows:print('\nID',r['mathdb_id'],r['record']['title'],'\n'+r['statement']+'\nSOURCE '+str(r['record']['source_url']))
