from pathlib import Path
import json,hashlib,re,zipfile
D=Path(__file__).resolve().parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(R)==20 and set(R)==set(map(str,ids))
for i,r in R.items():
 raw=D/'raw'/f'{i}.jsonl';b=raw.read_bytes();assert b.endswith(b'\n');assert sha(raw)==r['provenance']['raw_sha256'];o=json.loads(b)
 assert o['statement']==r['statement'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
 for f in r['source_files']:assert sha(D/f['path'])==f['sha256']
 assert r['accepted_credit']==0
for name,n,packet in [('replay.json',68,'nonchalant-source.zip'),('dprime-replay.json',43,'dprime-source.zip')]:
 o=json.loads((D/'outputs'/name).read_text());assert o['status']=='PASS';assert o['mathematical_module_declarations']==n;assert sha(D/packet)==o['packet_sha256']
 with zipfile.ZipFile(D/packet) as z:
  for f in z.namelist():
   assert '/' not in f and f.endswith('.lean')
   assert z.read(f)==(D/'lean'/f).read_bytes()
for n in ['Nonchalant','DPrime']:
 text=(D/'lean'/f'{n}.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',text)
 assert (D/'logs'/('fresh-audit.log' if n=='Nonchalant' else 'dprime-fresh-audit.log')).read_text().rstrip().endswith('TOTAL '+('68' if n=='Nonchalant' else '43'))
for lab in ['fresh-build','fresh-audit','fresh-leanchecker','dprime-fresh-build','dprime-fresh-audit','dprime-fresh-leanchecker']:
 assert json.loads((D/f'logs/{lab}.receipt.json').read_text())['returncode']==0
P=[]
for p in (D/'logs').glob('*.receipt.json'):P.append({'label':p.stem,**json.loads(p.read_text())})
(D/'outputs/processes.json').write_text(json.dumps(P,indent=2)+'\n')
out=dict(status='PASS',results=20,raw_lines_verified=20,packets_verified=2,accepted_credit=0,qualification='349435 source-version HOLD; 350350 cited-classical-construction exclusion recommended; independent review and root acceptance pending')
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
