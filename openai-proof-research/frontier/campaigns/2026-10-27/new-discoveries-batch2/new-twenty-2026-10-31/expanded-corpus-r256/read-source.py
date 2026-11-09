import pathlib,re
L=pathlib.Path(__file__).resolve().parent
for a in ['1405.4535','1405.6929','1406.5996','1407.5480','1407.5803','1407.7388','1407.7839','1409.1348','1409.2250','1409.4054','1409.6874','1409.6960']:
 lines=(L/(a+'.txt')).read_text().splitlines();print('\nSOURCE',a)
 hits=[i for i,t in enumerate(lines) if re.match(r'^Conjecture|^Problem|^Question',t)]
 if not hits:hits=[i for i,t in enumerate(lines) if 'conjecture' in t.lower()][:3]
 for i in hits[:7]:print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-1),min(len(lines),i+7))))
