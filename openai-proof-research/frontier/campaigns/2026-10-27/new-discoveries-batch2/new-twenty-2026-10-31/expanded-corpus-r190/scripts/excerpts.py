import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in sorted((D/'sources').glob('*-v*.txt')):
 ls=p.read_text().splitlines();out.append('\nFILE '+p.name)
 for j,l in enumerate(ls):
  if re.search(r'Conjecture (?:25|3\.29|7\.3|4\.10|2\.4|9\.6|3\.12|1\.|[1-5]\.?)\b',l):out.append('\n'.join(f'{k+1}: {ls[k]}' for k in range(max(0,j-1),min(j+9,len(ls)))))
(D/'outputs/version-excerpts.txt').write_text('\n'.join(out))
