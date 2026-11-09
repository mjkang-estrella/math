import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text());assert set(map(int,r))==set(reservation['ids']) and len(r)==20
versions=json.loads((D/'outputs/versions.json').read_text())
extra={'356542':['2312.11951'],'351566':['2106.12065','2204.12433'],'347518':['2310.03849'],'342736':['2101.04561'],'344348':['1912.10341'],'402063':['owr']}
for i,o in r.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==o['provenance']['raw_sha256'];obj=json.loads(raw);assert obj['statement']==o['statement'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256']
 o['advertised_arxiv_versions']=versions.get(o['source_url'].rsplit('/',1)[-1]+'-abs.html',[])
 for a in extra.get(i,[]):
  for p in (D/'sources').glob(a+'*receipt.json'):
   rec=json.loads(p.read_text());o['source_receipts'].append({'receipt':str(p.relative_to(D)),**{k:rec.get(k) for k in ['url','status','sha256','bytes','utc']}})
 if i=='342385':o['finite_checks']=[{'n':n,'dimensions':[(v['i'],v['dimension']) for v in vals if v['n']==n]} for vals in [json.loads((D/'outputs/kasami9.json').read_text()),json.loads((D/'outputs/kasami13.json').read_text())] for n in sorted(set(v['n'] for v in vals))]
 if i=='342736':o['finite_checks']=[json.loads((D/'outputs'/f'hyper-{n}-{k}.json').read_text()) for n,k in [(6,4),(7,5)]]
 if i=='344800':
  v=json.loads((D/'outputs/semigroups-28.json').read_text());assert not v['violations'];o['finite_checks']={'genus_max':28,'last_level':v['rows'][-1],'total_through_28':sum(x['total'] for x in v['rows']),'inequality_genus_max':27,'violations':[]}
 if i=='340116':o['finite_checks']=json.loads((D/'outputs/latin6.json').read_text())
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
receipts=[]
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());body=p.with_name(p.name[:-len('.receipt.json')])
 if 'sha256' in o:assert body.exists() and sha(body.read_bytes())==o['sha256'],str(p)
 receipts.append({'receipt':str(p.relative_to(D)),**{k:o.get(k) for k in ['url','status','utc','sha256','bytes','error']}})
(D/'outputs/http-receipt-index.json').write_text(json.dumps(receipts,indent=2))
status=collections.Counter(o.get('status',o.get('error')) for o in receipts)
check={'exactly_20_ids':True,'raw_and_statement_hashes_pass':True,'http_receipts_checked':len(receipts),'http_status_counts':dict(status),'new_results_claimed':0,'lean_endpoints_claimed':0,'numerical_checks_are_diagnostics':True}
(D/'outputs/validation.json').write_text(json.dumps(check,indent=2))
files=[p for p in D.rglob('*') if p.is_file() and p.name!='MANIFEST.json'];(D/'MANIFEST.json').write_text(json.dumps({str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(files)},indent=2)+'\n')
print(json.dumps(check));print('outcomes',dict(collections.Counter(o['outcome'] for o in r.values())))
