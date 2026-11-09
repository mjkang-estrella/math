exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
targets={
 'wotzlaw-thesis':r'Athanasiadis|Theorem 4\.|Corollary 4\.',
 'evenzohar':r'Theorem 2|F\(K\)|piecewise',
 'tight-construction':r'Corollary 1.3|Theorem 1.2',
 '0912.2916':r'Theorem 4.3',
 '0812.3082':r'Xi :=|Xi =|X1 :=|X1 =',
}
for a,pat in targets.items():
 lines=(l/'sources'/(a+'-pdf.txt')).read_text().splitlines();inds=set()
 for j,line in enumerate(lines):
  if re.search(pat,line):inds.update(range(max(0,j-4),min(len(lines),j+25)))
 print('SOURCE',a);print('\n'.join(f'{j+1}: {lines[j]}' for j in sorted(inds)[:85]))
for a,start,end in [('snevily-1004.0253',100,190),('multiset-journal',223,270)]:
 lines=(l/'sources'/(a+'-pdf.txt')).read_text().splitlines();print('PROOF',a);print('\n'.join(f'{j+1}: {lines[j]}' for j in range(start-1,min(end,len(lines)))))
