import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parents[1]; O=L/'resumed-20261105'; rows=[]
for p in sorted((L/'receipts').glob('*.json')):
 r=json.loads(p.read_text()); b=L/'receipts'/r.get('body_file','MISSING'); ok=b.exists() and hashlib.sha256(b.read_bytes()).hexdigest()==r.get('sha256'); rows.append({'receipt':str(p.relative_to(L)),'verified':ok,'url':r['url'],'status':r['status']})
 if ok and b.read_bytes()[:4]==b'%PDF':
  a=r['url'].rsplit('/',1)[1]; subprocess.run(['pdftotext','-layout',str(b),str(O/'text'/f'{a}.txt')],check=True)
p=json.loads((L/'outputs/provenance.json').read_text()); checks={}
for k,v in p.items():
 raw=(L/'inputs'/f'{k}.raw.jsonl').read_bytes(); cp=pathlib.Path(v['chunk']); actual=next(x for i,x in enumerate(cp.open('rb'),1) if i==v['line_1based']); checks[k]={'raw_ok':raw==actual and hashlib.sha256(raw).hexdigest()==v['raw_sha256'],'statement_sha256':hashlib.sha256(v['record']['statement'].encode()).hexdigest()}
(O/'inventory-verification.json').write_text(json.dumps({'receipts':rows,'raw_records':checks},indent=2));print('Receipts',len(rows),'verified',sum(r['verified'] for r in rows),'records',len(checks));print('\n'.join(str(r) for r in rows if not r['verified']))
for k,v in p.items():
 a=v['record']['source_url'].rsplit('/',1)[1]; t=(O/'text'/f'{a}.txt').read_text(); print(k,a,t[:160].replace('\n',' '));
