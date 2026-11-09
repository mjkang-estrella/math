import json,hashlib,pathlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r729';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 a=bind(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
def w(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
# Independently verify intake exact payload; do not invoke upstream code.
m=j(I/'manifest.json');names={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
refs=[bind(I/'manifest.json'),bind(I/'verification-receipt.json')]
for e in m['files']:check(I/e['path'],e);refs.append(bind(I/e['path']))
for e in j(I/'bindings.json'):
 for k in ('original','copy'):check(pathlib.Path(e[k]),e);refs.append(bind(pathlib.Path(e[k])))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);refs.append(bind(C/e['path']))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 refs.append(bind(p))
w('flat-bindings.json',list({r['path']:r for r in refs}.values()))
w('pre-reading-checks.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'original_copy_pairs':len(j(I/'bindings.json')),'chunks_in_place':20,'frozen_inputs':8,'upstream_code_executed':False})
print('VERIFIED and bound prerequisites')
# Scientific reading may begin only after the preceding checks and bindings.
q=j(I/'queue-r730.json');res=j(I/'reserved-ids-r730.json');cov=j(I/'coverage-delta.json');active=j(I/'active-breadth-reservations.json');assert len(cov)==9133
ids={r['mathdb_id'] for r in q};assert len(q)==len(ids)==50 and ids==set(res['ids']);seen=set()
for a in active:
 s=set(a['ids']);assert not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
assert len(seen)==150
records=[]
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:records.append({'corpus_path':e['path'],'corpus_line':n,'record':r})
assert len(records)==50
w('literal-records.json',records)
print('Reservations disjoint. Record keys:',records[0]['record'].keys())
for r in records:
 x=r['record'];print('\nID',x['mathdb_id'],x.get('title'),'\n',x['statement'],'\nSOURCE',x.get('references',x.get('source')))
