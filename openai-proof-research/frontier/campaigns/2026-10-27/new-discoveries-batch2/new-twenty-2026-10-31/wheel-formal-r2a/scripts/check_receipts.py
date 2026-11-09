from pathlib import Path
import json,re,hashlib,zipfile
D=Path(__file__).resolve().parent.parent
r=json.loads((D/'results.json').read_text())['371637']; L=D/'final-replay/logs'
mods=list(r['modules']);counts={};receipts={}
for m in mods:
 p=L/('audit-'+m+'.log');s=p.read_text()
 count=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',s).group(1))
 assert count==r['modules'][m]['declaration_count_including_generated']
 assert s.count('\nMODULE '+m+'\n')==count
 assert s.count('\nUNSAFE false\n')==count
 assert s.count('\nPARTIAL false\n')==count
 assert s.count('\nBODY ')==count
 assert s.count('\nAXIOMS ')==count
 assert '⋯' not in s and 'error:' not in s
 counts[m]=count
 for k in [m+'.log','audit-'+m+'.log','leanchecker-'+m+'.log']:
  rec=json.loads((L/(k+'.receipt.json')).read_text()); assert rec['exit_code']==0 and rec['killed_reason'] is None
  receipts[k]=rec
assert sum(counts.values())==160
for name in ['false','missing-bound','missing-independence','wrong-arithmetic']:
 k='negative-'+name+'.log';rec=json.loads((L/(k+'.receipt.json')).read_text());assert rec['exit_code']==1 and rec['killed_reason'] is None
 assert 'error:' in (L/k).read_text();receipts[k]=rec
assert 'Refusing existing oleans' in (L/'negative-existing-oleans.log').read_text()
assert json.loads((D/'logs/final-replay-driver.log').read_text().splitlines()[-1])['status']=='r2a_lower_bound_replayed'
for name,h in json.loads((D/'manifest.json').read_text()).items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==h
for name,h in json.loads((D/'inputs-before.json').read_text()).items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h
assert (D/'inputs-before.json').read_bytes()==(D/'inputs-after.json').read_bytes()
with zipfile.ZipFile(D/'wheel-lower-source.zip') as z:
 assert not any(n.endswith(('.olean','.ilean','.pyc')) for n in z.namelist())
 for name in z.namelist():assert z.read(name)==(D/name).read_bytes()
report={'371637':{'status':'PASS_r2a_scope_only','root_acceptance':'pending','credit':0,'declarations_by_module':counts,'declarations_total':sum(counts.values()),'proof_modules':mods,'negative_controls_passed':5,'inputs_unchanged':True,'packet_source_only':True,'source_manifest_verified':True,'max_successful_sampled_private_rss_bytes':max(x['peak_sampled_private_rss_bytes'] for x in receipts.values()),'receipts':receipts}}
(D/'final-verification.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report['371637'].items() if k!='receipts'},indent=2))
