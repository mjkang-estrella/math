#!/usr/bin/env python3
"""Read-only independent packet checks. Run through the prescribed helper guard."""
import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r431';C=L/'pi-mathdb-full-corpus-inventory-r301'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def load(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 require(p.is_file(),'missing '+str(p));require(('size' not in e and 'bytes' not in e) or p.stat().st_size==e.get('size',e.get('bytes')),'size '+str(p));require(sha(p)==e['sha256'],'sha '+str(p))
def canon(r):return hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')).hexdigest()
# Independently validate payload path set and byte bindings; no upstream code executed.
m=load(O/'manifest.json');entries=m['files'];paths=[e['path'] for e in entries];require(len(paths)==len(set(paths)),'duplicate payload path')
excluded={'manifest.json','final-receipt.json'}
actual={p.relative_to(O).as_posix() for p in O.rglob('*') if p.is_file()}-excluded
require(actual==set(paths),'exact payload set mismatch: '+repr(actual^set(paths)))
for e in entries:
 require(not pathlib.Path(e['path']).is_absolute() and '..' not in pathlib.Path(e['path']).parts,'unsafe path');check(O/e['path'],e)
bindings=load(O/'bindings.json');bound={e['original']:e for e in bindings};require(len(bound)==len(bindings),'duplicate original')
for e in bindings:check(pathlib.Path(e['original']),e)
require(str(I/'manifest.json') in bound and str(C/'manifest.json') in bound,'missing original manifests')
for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 p=pathlib.Path(e['original']);require(str(p) in bound,'unbound r431 direct original');check(p,e)
cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];require(len(chunks)==20,'twenty chunks')
for e in chunks:
 require('bytes' in e,'r301 bytes missing');check(C/e['path'],e);require(str(C/e['path']) in bound,'chunk unbound')
for pat,names in [('*r304',['manifest.json','accepted-exclusions.json','historical-dispositions.json']),('*r363',['manifest.json','disposition.json','coverage-delta.json','reserved-ids.json'])]:
 p=next(L.glob(pat));mm=load(p/'manifest.json');ee={x['path']:x for x in (mm['files'] if isinstance(mm,dict) else mm)}
 for n in names:
  require(str(p/n) in bound,'missing administrative binding');check(p/n,bound[str(p/n)])
  if n in ee:check(p/n,ee[n])
a=load(I/'reserved-ids.json');ids=set(a['ids']);require(len(a['ids'])==len(ids)==50,'fifty assignment');require({x['mathdb_id'] for x in load(I/'queue.json')}==ids,'queue assignment')
base=load(I/'coverage-delta.json');require(len(base)==2183,'baseline');require(len(a['other_active_reservations'])==50,'active count')
require(not ids&({int(k) for k in base}|set(a['other_active_reservations'])|{372627,372628,368940,404067,364119}),'assignment overlap')
def allids(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if str(k).isdigit():out.add(int(k))
   if k in ('mathdb_id','mathdb_related_id') and isinstance(v,int):out.add(v)
   out|=allids(v)
 elif isinstance(x,list):
  for v in x:out|=allids(v)
 return out
p304=next(L.glob('*r304'))
for name in ['accepted-exclusions.json','historical-dispositions.json']:require(not ids&allids(load(p304/name)),'historical overlap')
original={};locations={}
for e in chunks:
 p=C/e['path']
 with p.open() as f:
  for n,line in enumerate(f,1):
   r=json.loads(line);i=r['mathdb_id']
   if i in ids:
    require(i not in original,'duplicate corpus id');original[i]=r;locations[i]=(str(p),n)
require(set(original)==ids,'original assignment missing')
rs=load(O/'records.json');ds=load(O/'dispositions.json');ll=load(O/'record-locations.json');require(len(rs)==len(ds)==len(ll)==50,'fifty payload rows')
require({r['mathdb_id'] for r in rs}=={d['mathdb_id'] for d in ds}=={r['mathdb_id'] for r in ll}==ids,'payload IDs')
for r in rs:require(r==original[r['mathdb_id']],'record altered')
for d in ds:
 i=d['mathdb_id'];r=original[i];require(d['literal_statement']==r['statement'],'literal altered');require(d['literal_statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest(),'literal hash');require(d['canonical_record_sha256']==canon(r),'canonical hash');require(d['accepted_credit']==0 and d['prior_cleared'] is False,'unsupported credit')
for e in ll:
 i=e['mathdb_id'];require((e['original'],e['line'])==locations[i],'location');require(e['canonical_sha256']==canon(original[i]),'location canonical');require(e['statement_sha256']==hashlib.sha256(original[i]['statement'].encode()).hexdigest(),'location literal')
for e in load(O/'source-provenance.json'):
 if 'file' in e:check(O/e['file'],e)
for e in load(O/'source-excerpts.json'):
 lines=(O/e['file']).read_text().splitlines(keepends=True);require(e['text']==''.join(lines[e['first_line']-1:e['last_line']]),'excerpt altered')
require(load(O/'proposals.json')==[],'unexpected proposal');require(load(O/'provenance.json')['counts_unchanged']=={'additional':9,'total':39,'next':40},'counts changed')
print('PASS: exact 50 statements; originals and 20 chunks; disjointness; literal/canonical hashes; source excerpts; exact payload set. Scientific proof closure and novelty are not certified.')
