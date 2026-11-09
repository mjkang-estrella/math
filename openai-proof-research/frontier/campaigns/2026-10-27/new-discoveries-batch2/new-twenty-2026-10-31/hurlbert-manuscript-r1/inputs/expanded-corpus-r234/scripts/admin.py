import pathlib,json,re,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
ids=json.loads((D/'reservation.json').read_text())['ids']
patt='|'.join(map(str,ids))
r=subprocess.run(['rg','-n','--max-columns','700','--max-columns-preview',r'\b('+patt+r')\b',str(B),'-g','*.md','-g','results.json','-g','ledger.json','-g','!**/sources/**','-g','!**/raw/**'],text=True,capture_output=True)
(D/'history-exact.txt').write_text('\n'.join(x for x in r.stdout.splitlines() if '/expanded-corpus-r234/' not in x)+'\n')
ledger=json.loads((D.parent/'ledger.json').read_text()); prior=json.loads((B/'prior-campaign-context.json').read_text())
(D/'notes/admin.json').write_text(json.dumps({'ledger_sha256':hashlib.sha256((D.parent/'ledger.json').read_bytes()).hexdigest(),'ledger_keys':list(ledger),'accepted_ids':[x.get('mathdb_id') for x in ledger.get('accepted',[])],'prior_context_keys':list(prior)},indent=2))
tree=json.loads((D/'sources/pool-tree.body').read_text());pat=re.compile('quasipolar|walkmatrix|walkdet|rootedproduct|mtriangle|shufflelattice|dihedral|hurlbert|macchia|hackenbush|strut|haros|chern|separationnumber|locallyirregular|strongedge|subgrouptotal',re.I)
(D/'notes/pool-matches.json').write_text(json.dumps({'head':json.loads((D/'sources/pool-head.body').read_text())['sha'],'tree_sha':tree['sha'],'truncated':tree.get('truncated'),'matches':[x for x in tree['tree'] if pat.search(x['path'])]},indent=2))
for p in (D/'sources').glob('*-abs.body'):
 t=p.read_text();print(p.name,re.findall(r'\[v[0-9]+\]',t))
