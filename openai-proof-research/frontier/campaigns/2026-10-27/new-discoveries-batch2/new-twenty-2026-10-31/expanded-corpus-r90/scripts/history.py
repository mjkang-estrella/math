import pathlib,json,subprocess,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());P=D.parents[3]
pat='|'.join(r'\b'+i+r'\b' for i in x)+'|'+'|'.join(re.escape(o['title']) for o in x.values())
r=subprocess.run(['rg','-n','-i',pat,str(P),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json'],capture_output=True,text=True)
lines=[l for l in r.stdout.splitlines() if str(D)+'/' not in l]
(D/'outputs/history-exact.txt').write_text('\n'.join(lines)+'\n')
files=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']
review={}
for p in files:
 b=p.read_bytes();o=json.loads(b);review[str(p.resolve())]={'sha256':hashlib.sha256(b).hexdigest(),'accepted':o.get('accepted',[]),'excluded':o.get('excluded',[]),'candidates':o.get('candidates',[])}
(D/'outputs/inherited-family-review.json').write_text(json.dumps(review,indent=2)+'\n')
print('history lines',len(lines))
