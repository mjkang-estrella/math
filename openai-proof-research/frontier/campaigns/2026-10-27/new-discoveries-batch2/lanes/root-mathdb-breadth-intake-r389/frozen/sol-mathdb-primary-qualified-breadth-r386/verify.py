import pathlib,json,hashlib,sys,datetime
L=pathlib.Path(__file__).resolve().parent
EXCLUDED={'manifest.json','verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes()
 if len(b)!=e.get('size',e.get('bytes')) or digest(b)!=e['sha256']:raise ValueError('CHANGED: '+str(p))
def exactset(actual,expected):
 if actual!=expected:raise ValueError('PAYLOAD_SET: missing='+str(sorted(expected-actual))+' extra='+str(sorted(actual-expected)))
def check_manifest(base,m,exact=False):
 entries=m['files'];expected={e['path'] for e in entries}
 if len(expected)!=len(entries):raise ValueError('duplicate manifest path')
 for e in entries:check(base/e['path'],e)
 if exact:
  actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() and str(p.relative_to(base)) not in EXCLUDED}
  exactset(actual,expected)
def main():
 check_manifest(L,load(L/'manifest.json'),True)
 f=load(L/'input-bindings.json'); refs=f['references']
 if len({e['path'] for e in refs})!=len(refs):raise ValueError('duplicate original')
 for e in refs:check(pathlib.Path(e['path']),e)
 B=L.parent;R=B/'root-mathdb-circulant-park-intake-r385';C=B/'pi-mathdb-full-corpus-inventory-r301'
 check_manifest(R,load(R/'manifest.json'))
 for e in load(R/'bindings.json'):check(pathlib.Path(e['original']),e)
 r=load(R/'reserved-ids.json');ids=r['ids'];a=set(ids);cov=load(R/'coverage-delta.json');other=r['other_active_reservations']
 assert ids==f['reserved_ids'] and len(ids)==len(a)==50
 assert other==f['other_active_reservations'] and len(set(other))==50
 assert sorted(map(int,cov))==f['reviewed_ids'] and len(cov)==1033
 assert not a&set(other) and not a&set(map(int,cov)) and not a&{372627,372628,368940}
 chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 # All chunks checked before any statement content is selected.
 for e in chunks:check(C/e['path'],e)
 statements={};paths={}
 for e in chunks:
  p=C/e['path']
  with p.open() as h:
   for line in h:
    row=json.loads(line)
    if row['mathdb_id'] in a:
     i=row['mathdb_id'];assert i not in statements;statements[i]=row['statement'];paths[i]=str(p)
 assert set(statements)==a
 rows=load(L/'dispositions.json'); ss=load(L/'statements.json')
 assert len(rows)==len(ss)==50 and [x['mathdb_id'] for x in rows]==ids
 for collection in [rows,ss]:
  assert {x['mathdb_id'] for x in collection}==a
  for x in collection:
   i=x['mathdb_id'];assert x['statement']==statements[i] and x['statement_sha256']==digest(statements[i].encode()) and x['corpus_path']==paths[i]
 for x in rows:
  assert x['exact_scope']==statements[x['mathdb_id']] and x['reason'] and x['evidence_level'] and x['credit']==0 and x['full_statement_read']
 assert load(L/'proposals.json')==[]
 for p in (L/'primary').glob('*.meta.json'):
  m=load(p);check(p.with_name(p.name.replace('.meta.json','.body')),m)
 print(json.dumps({'status':'PASS','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_files':len(load(L/'manifest.json')['files']),'flat_original_references':len(refs),'root_manifest_read_only':'PASS','original_corpus_chunks_verified':20,'literal_statements_verified':50,'exact_reservation':'PASS','disjoint_reviewed':1033,'disjoint_other_active':50,'disjoint_focused':[372627,372628,368940],'proposals':0,'credit':0,'counts_unchanged':{'additional':9,'total':39,'next':40},'registry':'HOLD','complete_dependency_audits':0},indent=2))
def selftest():
 f=load(L/'input-bindings.json');e=dict(f['references'][0]);p=pathlib.Path(e['path']);e['sha256']='0'*64
 try:check(p,e)
 except ValueError:print('PASS: changed-original digest rejected nonzero-path without modifying any original')
 else:raise RuntimeError('original change not detected')
 p=L/'SUMMARY.md';e={'size':p.stat().st_size,'sha256':'0'*64}
 try:check(p,e)
 except ValueError:print('PASS: changed-payload digest rejected without modifying payload')
 else:raise RuntimeError('payload change not detected')
 for actual,expected in [({'a','extra'},{'a'}),(set(),{'missing'})]:
  try:exactset(actual,expected)
  except ValueError:print('PASS: exact payload set rejects missing/extra entry')
  else:raise RuntimeError('set change not detected')
if __name__=='__main__':
 if '--self-test' in sys.argv:selftest()
 else:main()
