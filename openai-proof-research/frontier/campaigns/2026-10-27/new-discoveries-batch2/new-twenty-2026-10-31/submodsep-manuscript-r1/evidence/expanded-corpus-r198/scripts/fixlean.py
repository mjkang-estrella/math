import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];p=D/'lean/Certificate.lean';s=p.read_text();z=json.loads((D/'outputs/submod-dual-compressed.json').read_text())
for k,a in enumerate(z['support']):
 pts=[x for x,c in a['terms']] if a['kind']=='submodular' else [a['point']]
 norms=[f'norm{x} f' for x in sorted(set(pts)) if f'lemma norm{x} ' in s]
 s=re.sub(r' simp only \[[^\n]*\] at h'+str(k)+r'\n',(' simp only ['+', '.join(norms)+f'] at h{k}\n') if norms else '',s)
p.write_text(s)
