import pathlib,json,re,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile('antimagic|mobius|bookgraph|crown|acyclicmatch|acyclic.match|seifert|gausscode|laplacianspread|multicone|neighborloc|neighbourloc|pillar|spherecol|bockstein|bollob|eldridge|almostsubgroup',re.I)
for name in ['openai','leanpool','omega']:
 p=D/f'sources/{name}-tree.json'
 if not p.exists(): continue
 o=json.loads(p.read_text()); rows=[x for x in o.get('tree',[]) if pat.search(x['path'])]
 (D/f'{name}-registry-matches.json').write_text(json.dumps({'truncated':o.get('truncated'),'head':json.loads((D/f'sources/{name}-head.json').read_text())['sha'],'matches':rows},indent=2))
 print(name,'truncated',o.get('truncated'),'matches',len(rows))
 for r in rows: print(r['path'])
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 o=json.loads(p.read_text()); print('context',p,'sha256',hashlib.sha256(p.read_bytes()).hexdigest(),'topkeys',list(o))
 (D/(p.parent.name+'-'+p.name)).write_text(json.dumps(o,indent=2))
