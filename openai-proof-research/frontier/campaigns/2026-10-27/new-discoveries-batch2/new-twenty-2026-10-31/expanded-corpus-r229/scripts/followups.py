import pathlib,json,subprocess
ns={'__file__':str(pathlib.Path(__file__).resolve().with_name('fetch.py')),'__name__':'fetch'}
exec(compile(pathlib.Path(ns['__file__']).read_text(),ns['__file__'],'exec'),ns);get=ns['get'];D=pathlib.Path(__file__).resolve().parents[1]
urls={
 'phylogenetic-followup.html':'https://link.springer.com/article/10.1007/s00026-026-00848-4',
 'aharoni-mathlib.html':'https://leanprover-community.github.io/mathlib4_docs/Counterexamples/AharoniKorman.html',
 'rigidity-followup.pdf':'https://qmro.qmul.ac.uk/xmlui/bitstream/handle/123456789/103251/Jackson%20Rigidity%20of%20Symmetric%202025%20Accepted.pdf?isAllowed=y&sequence=2',
 'isk4-followup.abs':'https://arxiv.org/abs/2610.32404',
 'aharoni-followup.abs':'https://arxiv.org/abs/2411.16844',
 'leanpool-readme.md':'https://raw.githubusercontent.com/Vilin97/lean-pool/'+json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha']+'/README.md',
 'leanpool-aharoni.lean':'https://raw.githubusercontent.com/Vilin97/lean-pool/'+json.loads((D/'sources/Vilin97-lean-pool-head.json').read_text())['sha']+'/LeanPool/AharoniKorman/Counterexample.lean',
}
for k,u in urls.items():get(k,u)
repo='openai/math';sha=json.loads((D/'sources/openai-math-head.json').read_text())['sha'];get('openai-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha)
p=D/'sources/openai-root.json'
if p.exists():
 for x in json.loads(p.read_text()).get('tree',[]):
  if x['path']=='preprints':get('openai-preprints-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1')
for p in (D/'sources').glob('*followup.pdf'):
 if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
