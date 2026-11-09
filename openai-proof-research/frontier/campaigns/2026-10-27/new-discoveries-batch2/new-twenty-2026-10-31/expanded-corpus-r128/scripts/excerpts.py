import pathlib,re
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*.txt')):
 lines=p.read_text().splitlines(); inds=[i for i,l in enumerate(lines) if re.match(r'^(Conjecture|Question|Problem|Open Question)\s',l)]
 out=[]
 for i in inds:
  out.extend(f'{j+1}: {lines[j]}' for j in range(max(0,i-5),min(len(lines),i+26)))
 (D/'outputs'/(p.stem+'-conjectures.txt')).write_text('\n'.join(out)+'\n')
