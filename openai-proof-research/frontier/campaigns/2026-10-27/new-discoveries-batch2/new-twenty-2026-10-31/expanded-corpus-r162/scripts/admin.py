import pathlib,json,subprocess,hashlib,urllib.request,datetime
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
r=json.loads((D/'reservation.json').read_text())
pats=[r'\b'+str(i)+r'\b' for i in r['ids']]+[x['title'] for x in r['rows']]
(D/'scripts/history-patterns-bounded.txt').write_text('\n'.join(pats))
p=subprocess.run(['rg','-n','-i','--max-columns','1200','-f',str(D/'scripts/history-patterns-bounded.txt'),str(B),'-g','*.md','-g','*results*.json','-g','*ledger*.json','-g','!**/expanded-corpus-r162/**'],capture_output=True,text=True)
(D/'history-bounded.txt').write_text(p.stdout)
for rel in ['ledger.json','new-twenty-2026-10-31/ledger.json','prior-campaign-context.json']:
 b=(B/rel).read_bytes(); o=json.loads(b)
 (D/'outputs'/('admin-'+rel.replace('/','-'))).write_text(json.dumps({'path':str(B/rel),'sha256':hashlib.sha256(b).hexdigest(),'content':o},indent=2))
for repo in ['openai/math','the-omega-institute/trureturing']:
 url='https://api.github.com/repos/'+repo+'/commits/HEAD'
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read();rec.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  o=json.loads(b);rec['head']=o['sha']
  (D/'sources'/('registry-'+repo.split('/')[-1]+'.json')).write_bytes(b)
 except Exception as e:rec['error']=str(e)
 (D/'sources'/('registry-'+repo.split('/')[-1]+'.receipt.json')).write_text(json.dumps(rec,indent=2))
 print(rec)
