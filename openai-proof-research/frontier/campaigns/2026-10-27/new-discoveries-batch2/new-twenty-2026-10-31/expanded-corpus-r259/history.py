import pathlib,re,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent;B=L.parent
pat=r'\b(?:328969|329015|329135|329353|329496|329533|329534|359739|364698|376094|381201|324804|324806|324816|325082|325147|325185|325239|325278|325280)\b|Babai.*[Ss]pectr|corolla coefficient|binary projections of episturmian'
r=subprocess.run(['rg','-n',pat,str(B),'-g','*.md','-g','*results.json','-g','*ruling*.json','-g','!expanded-corpus-r259/**'],capture_output=True,text=True,timeout=30)
lines=[x for x in r.stdout.splitlines() if '/expanded-corpus-r259/' not in x]
(L/'historical-matches.txt').write_text('\n'.join(lines)+'\n');print('\n'.join(lines)[:4000] or 'No literal ID/topic match in bounded campaign md/results/ruling search.')
for p in (B/'expanded-corpus-r252/http').glob('*tree.json'):
 j=json.loads(p.read_text());hits=[x['path'] for x in j.get('tree',[]) if re.search(r'Babai|episturm|Panyushev|Chapoton|Shigechi|Kolokol|GameDistinguish',x['path'],re.I)]
 print(p.name,j.get('truncated'),hits[:35])
