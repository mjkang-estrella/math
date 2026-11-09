#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
O=Path(__file__).resolve().parent;L=O.parent
EXCLUDE={'manifest.json','final-receipt.json'}
def need(v,msg):
 if not v:raise ValueError(msg)
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
def j(p):return json.loads(p.read_text())
def canonical(v):return json.dumps(v,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')
def check(p,x):
 h,n=digest(p);need(h==x['sha256'],f'hash mismatch: {p}')
 if 'size' in x or 'bytes' in x:need(n==x.get('size',x.get('bytes')),f'size mismatch: {p}')
 return n
try:
 manifest=j(O/'manifest.json');files=manifest['files'];want={x['path'] for x in files}
 need(len(want)==len(files),'duplicate payload paths');actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in EXCLUDE}
 need(want==actual,f'payload set mismatch: missing={want-actual}, extra={actual-want}')
 for x in files:
  need(not Path(x['path']).is_absolute() and '..' not in Path(x['path']).parts,'bad payload path');check(O/x['path'],x)
 binds=j(O/'bindings.json');need(len({x['original'] for x in binds})==len(binds),'duplicate original bindings')
 bound={x['original']:x for x in binds}
 for x in binds:check(Path(x['original']),x)
 audits={}
 for name in ['root-mathdb-breadth-intake-r435','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  p=L/name/'manifest.json';need(str(p) in bound,'unbound manifest');v=j(p);entries=v if isinstance(v,list) else v['files']
  for x in entries:
   dest=p.parent/x['path'];check(dest,x);need(str(dest.resolve()) in bound,'unbound manifest entry')
  audits[name]=len(entries)
 # Direct references only; do not expand any bound binding file recursively.
 direct=j(L/'root-mathdb-breadth-intake-r435/bindings.json')
 for x in direct:check(Path(x['original']),x);need(x['original'] in bound,'missing r435 direct original')
 inv=L/'pi-mathdb-full-corpus-inventory-r301';entries=j(inv/'manifest.json')['files'];chunkentries=[x for x in entries if x['path'].startswith('corpus/mathdb-normalized-chunk-') and x['path'].endswith('.jsonl')]
 need(len(chunkentries)==20,'original chunk count')
 for x in chunkentries:need('bytes' in x,'chunk bytes field missing');check(inv/x['path'],x)
 intake=L/'root-mathdb-breadth-intake-r435';assign=j(intake/'reserved-ids.json');ids=set(assign['ids']);q=j(intake/'queue.json');old=j(intake/'coverage-delta.json')
 need(len(ids)==len(assign['ids'])==50,'assignment count');need(assign['lane']==O.name,'wrong lane');need(len(q)==50 and ids=={x['mathdb_id'] for x in q},'queue assignment');need(len(old)==2283,'baseline count');need(len(assign['other_active_reservations'])==50,'other reservation count')
 need(not ids&set(assign['other_active_reservations']),'active overlap');need(not ids&set(map(int,old)),'baseline overlap');need(not ids&{372627,372628,368940,404067,364119},'excluded ID overlap')
 original={};locations={}
 for x in chunkentries:
  p=inv/x['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     k=r['mathdb_id'];need(k not in original,'duplicate original assigned ID');original[k]=r;locations[k]=(str(p),n)
 need(set(original)==ids,'original assigned missing')
 records=j(O/'records.json');need(len(records)==50 and {r['mathdb_id'] for r in records}==ids,'record set')
 for r in records:need(r==original[r['mathdb_id']],'canonical extraction changed')
 loc=j(O/'record-locations.json');need(len(loc)==50,'locations count')
 for x in loc:need(locations[x['id']]==(x['original'],x['line']),'wrong record location')
 ds=j(O/'dispositions.json');need(len(ds)==50 and {d['mathdb_id'] for d in ds}==ids,'disposition exact set')
 for d in ds:
  r=original[d['mathdb_id']];s=r['statement'];need(d['literal_statement']==s,'literal changed');need(d['literal_statement_sha256']==hashlib.sha256(s.encode()).hexdigest(),'statement hash');need(d['canonical_record_sha256']==hashlib.sha256(canonical(r)).hexdigest(),'canonical hash');need(bool(d['scope_and_reason']),'missing scope');need(d['credit']==0 and not d['prior_cleared'],'unsupported clearance')
 need(j(O/'proposals.json')==[],'unexpected brief');need(j(O/'provenance.json')['counts']=={'additional':9,'total':39,'next':40},'counts changed')
 for x in j(O/'source-excerpts.json'):
  lines=(O/x['source']).read_text().splitlines();need(x['text']=='\n'.join(lines[x['first_line']-1:x['last_line']]),'source excerpt mismatch')
 print(json.dumps({'status':'PASS','original_bindings':len(binds),'upstream_manifest_entries':audits,'original_chunks':20,'exact_assigned_dispositions':50,'baseline_reported_reviews':2283,'other_active_reservations':50,'payload_files':len(files),'proposals':0,'limitations':'integrity/assignment verifier; not a mathematical or novelty acceptance verifier'},sort_keys=True))
except Exception as e:
 print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
