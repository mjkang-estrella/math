import pathlib,json,re,subprocess
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
ids=json.loads((D/'reservation.json').read_text())['ids'];pat=r'\b(?:'+'|'.join(map(str,ids))+r')\b'
p=subprocess.run(['rg','-n','-i',pat,str(B),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json'],capture_output=True,text=True)
lines=[s for s in p.stdout.splitlines() if '/expanded-corpus-r187/' not in s and len(s)<1800]
(D/'outputs/history-filtered.txt').write_text('\n'.join(lines));print('\n'.join(lines[:35]));print('total',len(lines))
for path in [B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json']:
 obj=json.loads(path.read_text());(D/'outputs'/('families-'+path.parent.name+'.txt')).write_text('\n'.join(str(x.get('title',x)) for x in obj.get('accepted',[])))
