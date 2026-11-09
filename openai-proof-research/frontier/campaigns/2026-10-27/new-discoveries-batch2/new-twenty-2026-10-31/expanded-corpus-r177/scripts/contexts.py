import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
for i,o in json.loads((D/'extracted.json').read_text()).items():
 a=o['source_url'].rsplit('/',1)[-1];out=[]
 for p in sorted((D/'sources').glob(a+'*.txt')):
  ls=p.read_text().splitlines();out.append('\nFILE '+p.name)
  for j,l in enumerate(ls):
   if re.search(r'Conjecture|conjectur|Question',l):out.extend([f'LINE {j+1}',*ls[max(0,j-2):j+8]])
 (D/'outputs'/f'{i}-source-context.txt').write_text('\n'.join(out))
