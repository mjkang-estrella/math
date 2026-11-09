import pathlib,json,importlib.util,re
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
for a in ['2609.15081','2603.20961']:
 h.get(a+'.abs.html','https://arxiv.org/abs/'+a);h.get(a+'.pdf','https://arxiv.org/pdf/'+a)
h.get('neighborhood-followup.html','https://arxiv.org/abs/2401.04602')
# Recover all old version bodies; separate immutable receipts.
for p in list((D/'sources').glob('*.abs.html')):
 a=p.name.removesuffix('.abs.html');vs=re.findall(r'\[v(\d+)\]',p.read_text())
 for v in vs[:-1]:h.get(a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v)
t=json.loads((D/'sources/Vilin97-lean-pool-tree.json').read_text());sha=json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha']
for x in t['tree']:
 if x['path'].endswith('projects.yml'):h.get('pool-'+x['path'].replace('/','__'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/'+x['path'])
for fn in ['openai-math-tree.json','Vilin97-lean-pool-tree.json','the-omega-institute-trureturing-tree.json']:
 t=json.loads((D/'sources'/fn).read_text());pat=r'high.?order|hatguess|hat.guess|antimagic|polygoninter|feedbackgame|gao|principalsp|patternbound|arithmeticgraph|neighbo.rhoodideal|CMPP|bispectral|heptagon|signuncert|elongated|inverse.*sequence|inversionsequence'
 hits=[x for x in t['tree'] if re.search(pat,x['path'],re.I)];print(fn,'truncated',t.get('truncated'));print('\n'.join(x['path'] for x in hits)[:4500])
