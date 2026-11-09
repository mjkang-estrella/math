import pathlib,re,json
O=pathlib.Path(__file__).resolve().parent
with (O/'selected-passages.txt').open('w') as f:
 for p in sorted((O/'sources').glob('*.txt')):
  ls=p.read_text().splitlines(); hits=[i for i,l in enumerate(ls) if re.search(r'\bConjecture\s+\d+[. :()]',l)]
  f.write('\nSOURCE '+p.name+'\n')
  if not hits:hits=[max(0,len(ls)-100)]
  for i in hits[-3:]:
   f.write('\n'+str(i+1)+': '+'\n'.join(ls[max(0,i-2):i+15])+'\n')
