reads=[]
for row in R['rows']:
 idx=row['mathdb_id'];p=L/f'source-{idx}.txt';ls=p.read_text().splitlines();hits=[j for j,l in enumerate(ls) if re.search('conjecture|open problem',l,re.I)];used=set();print('\nPRIMARY',idx)
 for j in hits[:7]:
  for k in range(max(0,j-1),min(len(ls),j+7)):
   if k not in used:print(f'{k+1}: {ls[k]}');used.add(k)
 reads.append({'file':p.name,'sha256':H(p.read_bytes()),'emitted_one_based_lines':sorted(x+1 for x in used),'depth':'first seven conjecture/open-problem hits with context; rest acquired only'})
wj('primary-intake-read.json',reads)
for name in ['registry-openai','registry-leanpool','registry-tauceti']:
 t=(L/(name+'.txt')).read_text();print(name,'currentOid',re.findall(r'"currentOid":"([0-9a-f]+)"',t));print('paths',re.findall(r'"path":"([^"]+)"',t)[:60])
p=L.parents[5]/'sources/upstream.json';print('PINNED',p,p.read_text())
