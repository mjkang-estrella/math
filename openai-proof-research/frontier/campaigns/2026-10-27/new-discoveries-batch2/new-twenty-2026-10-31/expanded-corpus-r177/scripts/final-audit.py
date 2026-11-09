import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
for i,o in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
extra={'357873':['2506.01810.pdf','cover-published.pdf','ficarra-thesis.pdf'],'357904':['2312.02933.pdf'],'358134':['2603.11883.pdf'],'359132':['2610.19014.pdf'],'359205':['2509.17326.pdf'],'359206':['2411.12917.pdf'],'359268':['2609.12951.pdf'],'359474':['closure-path.pdf'],'359504':['haslegrave-published.pdf']}
for i,fs in extra.items():r[i]['supplemental_primary_receipts']=[json.loads((D/'sources'/(f+'.receipt.json')).read_text()) for f in fs]
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
a={'IDs':len(r),'all_raw_lines_and_statement_hashes_verified':True,'outcome_counts':dict(collections.Counter(o['outcome'].split('_')[0] for o in r.values())),'strong_surviving_leads':0,'Lean_endpoints':0,'credit_claimed':0};(D/'outputs/final-audit.json').write_text(json.dumps(a,indent=2));print(a)
