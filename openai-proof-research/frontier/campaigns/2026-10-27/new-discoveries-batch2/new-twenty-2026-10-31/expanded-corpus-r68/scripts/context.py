import pathlib,json,re,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent;B=C.parent;x=json.loads((D/'extracted.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
# Exact word boundaries avoid arithmetic-certificate digit substrings.
pats=[r'\b'+i+r'\b' for i in x]+[re.escape(o['title']) for o in x.values()]
(D/'scripts/history-regex.txt').write_text('\n'.join(pats)+'\n')
p=subprocess.run(['rg','-n','-i','--max-columns','1200','--max-columns-preview','-f',str(D/'scripts/history-regex.txt'),str(B),'-g','*.md','-g','*results*.json','-g','*review*.json','-g','*ledger*.json'],capture_output=True,text=True)
lines=[s for s in p.stdout.splitlines() if '/expanded-corpus-r68/' not in s]
(D/'history-matches.txt').write_text('\n'.join(lines)+'\n')
r={}
for scope,name,expected in [('D5','expanded-corpus-r65/sources/omega-D5.json','ef01560813e6f23dcc8a684a07e2d5b84986da41740aaa365c26cb32ffa9e9ce'),('Problems','expanded-corpus-r65/sources/omega-Problems.json','32c586c6d9458f95df35fe4814fff15aafb6eda5a2a7ba166b255a61e12c99d2'),('preprints','fresh-corpus-r10/sources/registry-preprints.json','6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305')]:
 p=C/name;b=p.read_bytes();assert sha(b)==expected;o=json.loads(b);tree=o.get('tree',[]);r[scope]={'path':str(p),'sha256':sha(b),'truncated':o.get('truncated'),'entries':len(tree),'id_path_hits':{i:[v['path'] for v in tree if re.search(r'(?<!\d)'+i+r'(?!\d)',v['path'])] for i in x}}
r['heads']={s:json.loads((D/'sources'/f'{s}-head.json').read_text())['sha'] for s in ['openai','omega']};r['limit']='Current heads match brief. Cached path scopes byte verified; no complete proof-body or deleted-history search.'
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
print('history lines',len(lines),'registry hits',[(k,i,h) for k,v in r.items() if isinstance(v,dict) for i,h in v.get('id_path_hits',{}).items() if h])
print('\n'.join(s[:350] for s in lines[:50]))
