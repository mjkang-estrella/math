import pathlib,json,hashlib,subprocess,re
D=pathlib.Path(__file__).resolve().parent; P=D.parent; B=P.parent
h=lambda b:hashlib.sha256(b).hexdigest()
files=[P/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/upstream.json'),pathlib.Path('openai-proof-research/sources/CONTENTS.md')]
o={}
for f in files:
 if f.exists():
  b=f.read_bytes();o[str(f)]={'sha256':h(b),'content':b.decode()}
(D/'ledger-context.json').write_text(json.dumps(o,indent=2))
r=json.load(open(D/'reservation.json')); patterns=[]
for row in r['rows']: patterns.extend([str(row['mathdb_id']),row['title']])
cmd=['rg','-n','-i','-F','--max-count','3','--glob','*.md','--glob','*.json','--glob','!reservation.json','--glob','!mathdb*','--glob','!registry*']
for s in patterns:cmd.extend(['-e',s])
cmd.append(str(B));z=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=45)
lines=[l for l in z.stdout.decode().splitlines() if '/expanded-corpus-r54/' not in l and '/corpus/' not in l and '/tags/' not in l]
(D/'history-search.txt').write_text('\n'.join(lines)+'\n');print('history lines',len(lines));print('\n'.join(x[:1000] for x in lines[:30]))
