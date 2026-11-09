import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1]
for p in (L/'sources').glob('*-tree/body'):
 x=json.loads(p.read_text());print(p.parent.name,'truncated',x.get('truncated'))
 paths=[z['path'] for z in x.get('tree',[])];(L/f'evidence/{p.parent.name}-paths.txt').write_text('\n'.join(paths))
 if 'leanpool' in str(p): print('\n'.join(paths[:80]))
