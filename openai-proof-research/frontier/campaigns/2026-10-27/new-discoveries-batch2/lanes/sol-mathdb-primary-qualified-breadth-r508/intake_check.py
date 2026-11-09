import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-banzhaf-retirement-intake-r503'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),str(p);assert h(b)==e['sha256'],str(p)
def bind(p):
 p=p.resolve();b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=h(b))
def run():
 refs={e['path']:e for e in j(P/'initial-bindings.json')}
 for e in refs.values():check(pathlib.Path(e['path']),e)
 m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(I/e['path'],e)
 flat=list(refs.values())
 for e in j(I/'bindings.json'):
  for key in ['original','copy']:
   p=pathlib.Path(e[key]);check(p,e);flat.append(bind(p))
 cm=j(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json');check(C/'manifest.json',bind(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:
  p=pathlib.Path(e['path']);p=p if p.is_absolute() else C/p;check(p,e);flat.append(bind(p))
 for name in ['sol-mathdb-primary-qualified-breadth-r500/flat-bindings.json','sol-mathdb-linear-two-tree-prior-boundary-r502/flat-actual-bindings.json']:
  for e in j(I/'frozen'/name):check(pathlib.Path(e['path']),e);flat.append(e)
 for pattern in ['*r304/accepted-exclusions.json','*r304/historical-dispositions.json','*r363/*decision*']:
  for p in L.glob(pattern):flat.append(bind(p))
 for p in [B/'ledger.json', B/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:flat.append(bind(p))
 unique={e['path']:e for e in flat};(P/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
 rs=j(I/'active-breadth-reservations.json');cov=j(I/'coverage-delta.json');assert len(cov)==3733
 allids=[]
 for r in rs:
  s=set(r['ids']);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(r['protected_ids']);allids+=r['ids']
 assert len(set(allids))==150
 for r in rs:assert set(r['other_active_reservations'])==set(allids)-set(r['ids'])
 mine=j(I/'reserved-ids-r508.json');assert mine in rs
 ids=set(mine['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r508.json')}
 rows=[]
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:rows.append(dict(ID=r['mathdb_id'],chunk=str(p.resolve()),line=n,literal=r['statement'],statement_utf8_sha256=h(r['statement'].encode()),canonical_record_sha256=h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),record=r))
 assert len(rows)==50 and {x['ID'] for x in rows}==ids
 (P/'statements.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps(dict(intake_files=len(m['files']),original_copy_pairs=len(j(I/'bindings.json')),chunks=20,frozen_inputs=8,flat_references=len(unique),assigned=50,baseline=3733)))
 print('history refs',[x for x in unique if 'r304/' in x or 'r363/' in x]);print('schema',rows[0]['record'].keys())
if __name__=='__main__':run()
