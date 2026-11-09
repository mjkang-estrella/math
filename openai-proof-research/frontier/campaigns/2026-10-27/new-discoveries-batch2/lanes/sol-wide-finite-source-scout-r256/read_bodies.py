from retrieve import L
import re,sys
hist=(L/'history-index.txt').read_text()
for m in re.finditer('2401.09497',hist):print('HISTORY',hist[m.start()-650:m.start()+1100])
for p in sorted((L/'sources').glob('*.txt')):
 if '-' in p.stem:continue
 s=p.read_text();print('\nSOURCE',p.stem)
 matches=list(re.finditer(r'(?m)^\s*(?:Conjecture|Question|Problem|Theorem)\s+[0-9A-Z]+[. :]',s))
 for m in matches[:8]:print(s[m.start():m.start()+1000])
