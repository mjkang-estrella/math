import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1];P=L.parent/'expanded-corpus-r212'
# Exact source quotations, line numbering inherited from hash-bound local text.
ranges={'v1':[(1,11),(118,181),(241,247),(360,374),(449,465),(515,532),(685,707),(870,954),(964,984)],'v2':[(1,12),(147,235),(556,572),(641,646),(1014,1091)],'v3':[(1,18),(139,229),(278,289),(618,628),(729,736),(1095,1131),(1154,1212)]}
with (L/'evidence/SOURCE-QUOTES.md').open('w') as o:
 for v,rs in ranges.items():
  name='2508.17854'+('' if v=='v3' else v)+'.txt'; lines=(P/'sources'/name).read_text().split('\n')
  o.write('# '+v+' — '+name+'\n\n')
  for a,b in rs:
   o.write('```text\n'+''.join(f'{i}: {lines[i-1]}\n' for i in range(a,b+1))+'```\n\n')
# Complete copies keep every example available, not just excerpted definitions.
for v in ['v1','v2','v3']:
 name='2508.17854'+('' if v=='v3' else v)+'.txt'
 (L/'evidence'/f'{v}-numbered.txt').write_text(''.join(f'{i}: {s}\n' for i,s in enumerate((P/'sources'/name).read_text().split('\n'),1)))
M=json.loads((L/'evidence/math.json').read_text())
for m,x in M['circuits'].items():print(m,x)
print('head',json.loads((L/'downloads/pool-head/body').read_text())['sha'])
print('candidate sha',hashlib.sha256((P/'CANDIDATE.md').read_bytes()).hexdigest())
