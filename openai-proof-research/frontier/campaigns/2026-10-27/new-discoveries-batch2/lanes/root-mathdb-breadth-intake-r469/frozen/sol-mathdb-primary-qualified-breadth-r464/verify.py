"""Independent integrity verification only. No upstream code imports/execution or writes."""
import pathlib,json,hashlib,sys
L=pathlib.Path(__file__).resolve().parent;B=L.parent

def require(v,msg):
 if not v:raise ValueError(msg)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def data(p):return json.loads(p.read_text())
def check(p,e):
 require(p.is_file(),'missing '+str(p));require(digest(p)==e['sha256'],'hash mismatch '+str(p))
 size=e.get('bytes',e.get('size'))
 if size is not None:require(p.stat().st_size==size,'size mismatch '+str(p))
def associations(o):
 out=set()
 if isinstance(o,list):
  for v in o:out|=associations(v)
 elif isinstance(o,dict):
  for k,v in o.items():
   if k in ['mathdb_id','problem_id'] and isinstance(v,int):out.add(v)
   elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list):out|={x for x in v if isinstance(x,int)}
   else:out|=associations(v)
 return out

def main():
 m=data(L/'manifest.json'); fs=m['files']; actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()};decl={e['path'] for e in fs}
 require(len(decl)==len(fs),'duplicate manifest paths');require(actual-{'manifest.json','final-receipt.json'}==decl,'exact payload membership mismatch')
 for e in fs:check(L/e['path'],e)
 bs=data(L/'bindings.json');ref={e['path']:e for e in bs};require(len(ref)==len(bs),'duplicate binding paths')
 for e in bs:check(pathlib.Path(e['path']),e)
 for lane in ['root-mathdb-breadth-intake-r463','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
  d=B/lane;check(d/'manifest.json',ref[str(d/'manifest.json')]);im=data(d/'manifest.json')
  for e in im if isinstance(im,list) else im['files']:check(d/e['path'],e)
  for e in data(d/'bindings.json'):
   # Flat only: validate exactly the actual original and its named copy; never follow its bindings.
   check(pathlib.Path(e['original']),e)
   if 'copy' in e:check(d/e['copy'],e)
 I=B/'pi-mathdb-full-corpus-inventory-r301';im=data(I/'manifest.json');chunks=[e for e in im['files'] if e['path'].startswith('corpus/')];frozen=[e for e in im['files'] if e['path'].startswith('frozen/')]
 require(len(chunks)==20,'not twenty chunks');require(data(L/'inventory-frozen-membership.json')==frozen,'inventory frozen membership mismatch')
 for e in chunks+frozen:check(I/e['path'],e)
 T=B/'root-mathdb-breadth-intake-r463';r=data(T/'reserved-ids.json');ids=r['ids'];queue=data(T/'queue.json');cov=data(T/'coverage-delta.json')
 require(r['lane']==L.name,'wrong lane');require(len(ids)==len(set(ids))==50,'wrong reservation cardinality');require(ids==[e['mathdb_id'] for e in queue],'queue assignment mismatch');require(len(cov)==2983,'baseline mismatch')
 excluded=associations(data(B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))|associations(data(B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json'))|{372627,372628,368940,404067,364119}
 require(not set(ids)&(excluded|set(map(int,cov))|set(r['other_active_reservations'])),'coverage/reservation/exclusion overlap')
 rec=data(L/'records.json');disp=data(L/'dispositions.json');require(len(rec)==len(disp)==50,'not exactly fifty rows');require([e['mathdb_id'] for e in disp]==ids,'disposition exact assignment mismatch');require([e['record']['mathdb_id'] for e in rec]==ids,'record order mismatch')
 originals={}
 for e in chunks:
  p=I/e['path']
  for line_no,line in enumerate(p.open(),1):
   o=json.loads(line)
   if o['mathdb_id'] in ids:
    require(o['mathdb_id'] not in originals,'duplicate corpus ID');originals[o['mathdb_id']]=(o,str(p),line_no)
 require(set(originals)==set(ids),'original set mismatch')
 for a,d,i in zip(rec,disp,ids):
  o,p,ln=originals[i];require(not o.get('historical'),'historical corpus flag')
  canonical=hashlib.sha256(json.dumps(o,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest();st=hashlib.sha256(o['statement'].encode('utf-8')).hexdigest()
  for row in [a,d]:
   require(row['record']==o,'literal canonical record mismatch');require(row['original_chunk']==p and row['original_line']==ln,'original locator mismatch');require(row['statement_utf8_sha256']==st and row['canonical_record_sha256']==canonical,'statement/canonical hash mismatch')
  require(d['literal_statement']==o['statement'],'literal disposition statement mismatch');require(d['accepted_credit']==0,'credit mutation');require(d['statement_read'] is True,'statement read flag')
 require(data(L/'proposals.json')==[],'unexpected proposal')
 for s in data(L/'sources.json')+data(L/'successor-bodies.json')+data(L/'successors.json'):
  if 'path' in s:check(pathlib.Path(s['path']),s)
  if 'text_sha256' in s:
   p=pathlib.Path(s.get('text_path',str(pathlib.Path(s['path']).with_suffix('.txt'))));require(digest(p)==s['text_sha256'],'retained text mismatch')
 if (L/'final-receipt.json').exists():
  receipt=data(L/'final-receipt.json');require(receipt['manifest_sha256']==digest(L/'manifest.json'),'receipt manifest binding mismatch');require(receipt['integrity']=='PASS' and receipt['accepted_credit']==0,'receipt state mismatch')
 return {'integrity':'PASS','statement_rows':50,'chunks_verified_in_place':20,'baseline_reported_reviews':2983,'public_statement_matches':6,'holds':44,'proposals':0,'accepted_credit':0,'whole_body_reads_claimed':0,'complete_dependency_audits_claimed':0,'MathDB_requests':0,'mathematics_pass':False,'novelty_pass':False,'counts':{'additional':9,'total':39,'next':40}}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print('INTEGRITY FAIL: '+str(e),file=sys.stderr);sys.exit(1)
