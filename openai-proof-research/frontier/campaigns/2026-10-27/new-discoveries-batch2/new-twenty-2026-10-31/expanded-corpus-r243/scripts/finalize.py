import pathlib,json,hashlib,collections,re,datetime
L=pathlib.Path(__file__).resolve().parents[1]
# Make the historical helper safe for future reproduction, without touching receipts.
p=L/'scripts/setup.py';s=p.read_text();s=s.replace("'-g','*.md','-g','results.json','-g','*.json'", "'-g','SUMMARY.md','-g','CANDIDATE.md','-g','results.json'")
p.write_text(s)
reg={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'heads':{},'github_repository_searches':[],'leanpool':'Complete tree, LeanPool/projects.yml and all blob files under candidates/ fetched at pinned HEAD. Terms and incidental hits in evidence/registry-screen.json. No matching proof found there; not an exhaustive proof-body audit.','scoped_registry_screen':'evidence/complete-registry-path-screen.json','limitation':'OpenAI root and Omega root recursive requests were truncated. Complete preprints/D5/Problems scopes fetched subsequently. Five GitHub repository metadata queries are bounded, not full code search or global proof clearance. No prior-art clearance claimed for any unresolved target.'}
for n in ['leanpool','openai','omega']:
 p=L/f'sources/{n}-head/body';x=json.loads(p.read_text());reg['heads'][n]={'sha':x['sha'],'receipt':f'sources/{n}-head/receipt.json'}
for d in sorted((L/'sources').glob('github-search-*')):
 rc=json.loads((d/'receipt.json').read_text());x=json.loads((d/'body').read_text());reg['github_repository_searches'].append({'url':rc['url'],'utc':rc['utc'],'status':rc['status'],'total_count':x.get('total_count'),'incomplete_results':x.get('incomplete_results'),'receipt':str((d/'receipt.json').relative_to(L)),'hits':[a.get('full_name') for a in x.get('items',[])]})
(L/'outputs/registry-screen.json').write_text(json.dumps(reg,indent=2)+'\n')
res=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];assert set(res)==set(map(str,ids));assert len(res)==20
for k,r in res.items():
 raw=(L/f'raw/{k}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256'];r['registry_screen'].append('outputs/registry-screen.json')
 for p in r['evidence']+r['primary_http_receipts']:assert (L/p).is_file(),p
(L/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
receipts=[]
for p in sorted((L/'sources').glob('*/receipt.json')):
 x=json.loads(p.read_text());b=p.parent/'body'
 if x.get('sha256'):assert b.is_file() and hashlib.sha256(b.read_bytes()).hexdigest()==x['sha256'],str(p)
 receipts.append({'receipt':str(p.relative_to(L)),**x})
(L/'evidence/http-receipt-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
cyc=[json.loads(s) for s in (L/'logs/cycle.txt').read_text().splitlines()];assert sum(x['multisets_tested'] for x in cyc)==1130629
m=json.loads((L/'logs/morse-verified.txt').read_text());assert m['full_integer_valuation']==9 and m['agree'] and m['full_integer_mod_5pow10']==7812500
# Structured validation metadata; no numerical claims are elevated to Lean endpoints.
audit={'records':len(res),'outcomes':dict(collections.Counter(r['outcome'] for r in res.values())),'http_receipts':len(receipts),'receipt_statuses':dict(collections.Counter(str(x.get('status',x.get('error'))) for x in receipts)),'raw_and_statement_hashes':'pass','receipt_body_hashes':'pass','all_evidence_paths':'pass','lean_endpoints':0,'accepted_credit':0,'numerical_scripts_isolated_bytecode_disabled':True}
(L/'outputs/validation.json').write_text(json.dumps(audit,indent=2)+'\n')
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name!='artifact-sha256.json'}
(L/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(audit,indent=2))
