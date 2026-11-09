import json,pathlib,re,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent;B=C.parent
ids=json.loads((D/'reservation.json').read_text())['ids'];pat=r'\b(?:'+'|'.join(map(str,ids))+r')\b'
p=subprocess.run(['rg','-n',pat,str(B),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json'],capture_output=True,text=True)
rows=[x for x in p.stdout.splitlines() if '/expanded-corpus-r242/' not in x]
(D/'history-exact-id-matches.txt').write_text('\n'.join(rows)+'\n')
r={}
for path in [C/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json']:
 data=path.read_bytes();o=json.loads(data);r[str(path)]={'sha256':hashlib.sha256(data).hexdigest(),'keys':list(o),'reserved_id_occurrences':[i for i in ids if re.search(r'\b'+str(i)+r'\b',data.decode())]}
(D/'inherited-ledger-review.json').write_text(json.dumps(r,indent=2)+'\n');print('bounded exact ID history matches',len(rows))
for row in rows:print(row[:800])
