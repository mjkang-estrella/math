import pathlib,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.pdf'):
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
s=json.loads((D/'sources/leanpool-head.json').read_text())['sha'];tree=json.loads((D/'sources/leanpool-tree.json').read_text());todo=[]
for o in tree['tree']:
 if o['path'].startswith('candidates/') and o['type']=='blob':todo.append(['pool-'+o['path'].replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/'+o['path']])
(D/'outputs/pool-plan.json').write_text(json.dumps(todo));print('candidate files',len(todo))
