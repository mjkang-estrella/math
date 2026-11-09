import pathlib,re,json
O=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((O/'sources').glob('*.txt')):
 lines=p.read_text().splitlines();hits=[i for i,l in enumerate(lines) if re.search(r'conjectur|problem [0-9]|theorem 1\.|question [0-9]|khintchin',l,re.I)]
 selected=set(range(min(22,len(lines))))
 for i in hits:
  selected.update(range(max(0,i-2),min(len(lines),i+7)))
 out='\n'.join(f'{i+1}: {lines[i]}' for i in sorted(selected));(O/'sources'/('passages-'+p.name)).write_text(out+'\n');print('\nFILE '+p.name+'\n'+out)
