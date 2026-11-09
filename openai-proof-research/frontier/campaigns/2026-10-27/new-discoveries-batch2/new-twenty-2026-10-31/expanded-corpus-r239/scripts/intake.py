import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 if p.exists():
  b=p.read_bytes();j=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(j),'accepted':j.get('accepted',[]),'excluded':j.get('excluded',[])}
(D/'ledger-read.json').write_text(json.dumps(out,indent=2)+'\n')
out={}
for p in (D/'sources').glob('*.txt'):
 if not re.match(r'\d{4}\.\d+',p.name):continue
 lines=p.read_text().splitlines();indices=[i for i,s in enumerate(lines) if re.search('conjectur|Conjectur',s)]; keep=set()
 for i in indices:
  keep.update(range(max(0,i-3),min(len(lines),i+9)))
 out[p.name]={'conjecture_context':'\n'.join(str(i+1)+': '+lines[i] for i in sorted(keep)),'printed_examples_figures':[str(i+1)+': '+s for i,s in enumerate(lines) if re.search(r'Figure\s+\d|Example\s+\d|Table\s+\d|Exemple\s+\d',s)]}
(D/'source-contexts.json').write_text(json.dumps(out,indent=2)+'\n')
print('ledgers read',[(p,x['keys']) for p,x in json.loads((D/'ledger-read.json').read_text()).items()]);print('source contexts',len(out))
