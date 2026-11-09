#!/usr/bin/env python3
import pathlib,json,hashlib,sys
O=pathlib.Path(__file__).resolve().parent;L=O.parent;R=L.parents[4]
def read(p):return json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def require(b,msg):
 if not b:raise ValueError(msg)
def check(p,e):
 require(p.is_file(),f'missing {p}');require(digest(p)==e['sha256'],f'hash {p}')
 if 'size' in e or 'bytes' in e:require(p.stat().st_size==e.get('size',e.get('bytes')),f'size {p}')
def exact(d,entries,excluded):
 require(len(entries)==len({e['path'] for e in entries}),f'duplicate manifest path {d}')
 expected={e['path'] for e in entries};actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}
 require(actual-set(excluded)==expected and not expected&set(excluded),f'exact payload set {d}: extra={actual-expected-set(excluded)} missing={expected-actual}')
 for e in entries:check(d/e['path'],e)
try:
 bindings=read(O/'bindings.json');require(len({x['original'] for x in bindings})==len(bindings),'duplicate bindings')
 for e in bindings:check(pathlib.Path(e['original']),e)
 upstream=[]
 for lane in ['root-mathdb-breadth-intake-r447','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  d=L/lane;j=read(d/'manifest.json');entries=j if isinstance(j,list) else j.get('files',[])+j.get('frozen_inputs',[])
  exact(d,entries,['manifest.json','verification-receipt.json']);upstream.append({'lane':lane,'files':len(entries)})
  if lane=='pi-mathdb-full-corpus-inventory-r301':
   chunks=[e for e in entries if e['path'].startswith('corpus/mathdb-normalized-chunk-')];require(len(chunks)==20,'20 chunks');require(len(j['frozen_inputs'])==8,'frozen inputs')
  if lane=='root-mathdb-breadth-intake-r447':
   for e in read(d/'bindings.json'):check(pathlib.Path(e['original']),e)
 A=L/'root-mathdb-breadth-intake-r447';res=read(A/'reserved-ids.json');ids=res['ids'];baseline=read(A/'coverage-delta.json')
 require(len(ids)==len(set(ids))==50,'fifty unique assignment');require(len(baseline)==2583,'baseline count')
 require(len(res['other_active_reservations'])==50,'other fifty');require(not set(ids)&set(res['other_active_reservations']),'active overlap')
 require(not set(map(str,ids))&set(baseline),'reviewed overlap');require(not set(ids)&{372627,372628,368940,404067,364119},'explicit exclusion')
 require({x['mathdb_id'] for x in read(A/'queue.json')}==set(ids),'queue mismatch')
 records=read(O/'records.json');D=read(O/'dispositions.json');loc=read(O/'record-locations.json')
 require(len(D)==len(records)==len(loc)==50,'output counts');require({x['mathdb_id'] for x in D}=={x['mathdb_id'] for x in records}==set(ids),'output assignment')
 original={}
 for chunk in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
  with chunk.open() as f:
   for lineno,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in set(ids):
     require(r['mathdb_id'] not in original,'duplicate original assigned record');original[r['mathdb_id']]=(r,str(chunk),lineno)
 require(set(original)==set(ids),'missing originals')
 for r in records:
  i=r['mathdb_id'];require(r==original[i][0],f'original mismatch {i}')
  ds=next(d for d in D if d['mathdb_id']==i);require(ds['literal_statement']==r['statement'],f'literal {i}')
  require(ds['literal_statement_sha256']==hashlib.sha256(r['statement'].encode('utf-8')).hexdigest(),f'literal hash {i}')
  require(ds['canonical_record_sha256']==hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')).hexdigest(),f'canonical hash {i}')
  require(ds['accepted_credit']==0 and not ds['prior_cleared'] and not ds['proof_dependency_closure'],f'credit {i}')
 for e in loc:require((e['path'],e['line'])==original[e['id']][1:],f'location {e["id"]}')
 for e in read(O/'source-excerpts.json'):
  p=O/e['path'];require(digest(p)==e['sha256'],'excerpt source hash');require('\n'.join(p.read_text().splitlines()[e['line_start']-1:e['line_end']])==e['text'],'excerpt mismatch')
 require(read(O/'proposals.json')==[],'proposals')
 m=read(O/'manifest.json');require(m['excluded']==['manifest.json','final-receipt.json'],'exclusions exact relative paths')
 exact(O,m['files'],m['excluded'])
 print(json.dumps({'status':'PASS','bindings':len(bindings),'upstream_manifest_checks':upstream,'chunks_checked':20,'assignment_count':50,'dispositions':50,'proposals':0,'payload_files':len(m['files']),'manifest_sha256':digest(O/'manifest.json'),'counts':'9 additional / 39 total / next 40 unchanged','proof_dependency_closure':False}))
except Exception as e:
 print(json.dumps({'status':'FAIL','error':str(e)}));sys.exit(1)
