from pathlib import Path
import subprocess,re,json
L=Path(__file__).resolve().parents[1]
for p in (L/'sources').glob('*.pdf'):
 if not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True)
# Every source's conjecture context, bounded excerpts retained for investigator reading.
out=[]
for p in sorted((L/'sources').glob('*.txt')):
 lines=p.read_text(errors='replace').splitlines();seen=set();s=[]
 for i,l in enumerate(lines):
  if re.search(r'Conjecture \d',l):
   for j in range(max(0,i-2),min(len(lines),i+12)):
    if j not in seen:s.append(f'{j+1}: {lines[j]}');seen.add(j)
 out.append(p.name+'\n'+'\n'.join(s))
(L/'outputs/source-conjecture-context.txt').write_text('\n\n'.join(out))
print('contexts retained',len(out))
